/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The claims

Each definition below is a proposition stating one claim of the paper, in terms of
Mathlib and the objects of `HubbardMoments.Defs`. `HubbardMoments.Main` proves each of
them. Reading this file and `Defs` is enough to know exactly what is proved; the proofs
can be checked by the machine.

| proposition | paper |
|---|---|
| `SectorDimensions` | sector-counting rule (§4, Fig. 3) |
| `SectorDimensionsQuoted` | the sector dimensions quoted in §4 |
| `HopAverage` | exact second-moment theorem, combinatorial part (§5.2) |
| `HopAverageRegular` | its `z`-regular form (§5.2) |
| `HopAverageTorus` | its square-lattice form (§5.2) |
| `HopAverageTorusValues` | `μ₂(U → ∞)` at `λ = 1` for `n = 4`, `L = 4, 5` |
| `ProjectedHoppingDiagonalZero` | `Tr H∞ = 0` (§5.2) |
| `ProjectedHoppingSquareDiagonal` | `(H∞²)_{cc} = λ² M(c)` (§5.2) |
| `SecondMomentTheorem` | the exact second-moment theorem (§5.2) |
| `SecondMomentRegular` | its `z`-regular form, used throughout the paper |
| `SecondMomentTorus` | its square-lattice form |
| `ProjectedHoppingExists` | the hypotheses above can be met (non-vacuity check) |
| `PairHoppingHermitian` | the two-electron model with Peierls phases is Hermitian (model check) |
| `DoublonFirstOrderZero` | no single hop connects two doublons (§8) |
| `DoubledPeierlsPhase` | the doublon hops with `t_d e^{2iA}`, `t_d = 2t²/U` (§8) |
| `DoublonHoppingRange` | at second order the doublon hops only to nearest neighbours |
| `DoublonOnSiteShift` | its energy shift `2 z t²/U` does not depend on the phases |
| `DoublonOnSiteShiftTorus` | `8 t²/U` on the square lattice |
| `TorusTriangleFree` | the `L × L` torus has a triangle exactly when `L = 3` |
| `SchriefferWolffCrossTerm` | `Tr(T₀ V) = 0` on triangle-free graphs (§7.2, App. D) |
| `SchriefferWolffSecondMoment` | hence `μ₂(T₀ - V/U) = μ₂(T₀) + Var(V)/U²`: no `1/U` term (§7.2) |
| `SchriefferWolffSecondMomentTorus` | the same on the square lattice, `L ≥ 4` |
| `CrossTermNeedsTriangleFree` | the hypothesis cannot be dropped: a nonzero cross term at `L = 3` |
| `SampleMean` | sampling without replacement from a centred population: mean `0` (§5.3) |
| `FinitePopulationVariance` | its variance `k σ₁² (N - k)/(N - 1)` (§5.3) |
| `FinitePopulationFourthMoment` | the sampling fourth-moment formula (App. B) |
| `IndependentSumSecondMoment` | second moments of independent variables add (one mean `0`) |
| `IndependentSumFourthMoment` | `μ₄(X + Y) = μ₄(X) + μ₄(Y) + 6 Var X Var Y` (App. B) |
| `TorusBandMoments` | the torus band: `∑ ε = 0`, `∑ ε² = 4t²L²`, i.e. `σ₁² = z t²` |
| `FreeFermionSecondMomentTorus` | second moment for one free species on the torus (§5.3) |
| `FreeAndProjectedSecondMomentsAgree` | one-species second moments agree at `U = 0` and `U = ∞` |
| `FinitePopulationTable` | the six values of the finite-population table (`L = 4`) |
| `ClosedWalkFewMoved` | a closed walk of `h` hard-core hops moves no particle or fewer than `h` |
| `FourHopPermutations` | the identity, transpositions and 3-cycles exhaust four hops (§6) |
| `FourHopExchangesOccur` | both types of exchange occur on every torus with `L ≥ 3` |
| `ThreeCycleCountAffine` | `P₃ = C(N↑,3) + C(N↓,3)` is affine in `P_same` at fixed `n` (§6) |
| `SortedTupleSignRule` | one hop: `c†_{o'} c_o \|S⟩ = (-1)^{m+p} \|S \ {o} ∪ {o'}⟩` (App. E) |
| `HubbardHoppingHermitian` | the hopping term `H_t` with Peierls phases is Hermitian |
| `HubbardHoppingIsHoppingOperator` | `H_t` connects only Fock states one hop apart |
| `ProjectedHubbardIsProjectedHopping` | `H∞ = P₀ H_t P₀` is projected hopping |
| `SecondMomentHubbard` | hence the exact second-moment theorem for `H∞` itself (§5.2) |
| `SecondMomentHubbardTorus` | its square-lattice form |
| `SchriefferWolffHubbard` | the cross term for `H_t` on triangle-free graphs (§7.2) |
| `SecondMomentWeightedTheorem` | the second-moment formula for bond-dependent moduli |
| `SecondMomentHubbardWeighted` | weighted second moment of `H∞` for Hermitian hopping (§5.2) |

## What these claims do not include

* Any statement about higher moments, finite `U` or flux beyond what `IsProjectedHopping`
  allows (it allows any Peierls phases, since only moduli enter).
* The second-order formula of degenerate perturbation theory (Schrieffer–Wolff) itself. The
  doublon claims evaluate its terms (`doublonSecondOrder`); the cross-term claims are about
  the operators `T₀ = P₀HP₀` and `V = T₁†T₁` that it produces.
* That `annihilate` and `create` are the physical fermion operators. They satisfy the
  sorted-tuple sign rule (`SortedTupleSignRule`), and the ordering `ord`
  of the orbitals, which fixes the signs of the basis states, is arbitrary. Any other
  convention differs from these by phases of the basis states, which change no modulus;
  that standard fact is not proved here.
* That the many-body energies of free fermions of one species are the sums of distinct
  single-particle energies (Slater determinants), and that `torusBand` is the spectrum of
  the hopping matrix of `torus L` (plane waves). Both are standard; they are what make
  `sampleMoment (torusBand L t)` the `U = 0` moments of the paper.
* The fermionic signs and spin conditions of the four-hop walks, and the resulting form
  `μ₄(∞) = A(N, n) + α(N, n) P_same`. The walk claims are about labelled hard-core
  particles and the permutations they can realize.
* That the paper's cross term, over a full sector at `L = 3`, is nonzero. That is a
  numerical result. `CrossTermNeedsTriangleFree` shows only that the general statement
  fails at `L = 3`, with a two-state `B` and a hand-built hopping operator.
-/

@[expose] public section

namespace HubbardMoments.Spec

open Finset

/-- **Sector dimensions.** For `k ≤ b`, the `k`-doublon sector of `a` up and `b` down
electrons on `N` sites has `C(N, a) · C(a, k) · C(N - a, b - k)` states. -/
def SectorDimensions : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (a b k : ℕ), k ≤ b →
    (sector V a b k).card =
      (Fintype.card V).choose a * a.choose k * (Fintype.card V - a).choose (b - k)

/-- **The quoted sector dimensions.** Two up and two down electrons on the 4 × 4 lattice:
10920, 3360 and 120 states with 0, 1 and 2 doublons. Two up and one down electron on the
5 × 5 lattice: 6900 and 600 states with 0 and 1 doublon. -/
def SectorDimensionsQuoted : Prop :=
  (sector (Fin 4 × Fin 4) 2 2 0).card = 10920 ∧
    (sector (Fin 4 × Fin 4) 2 2 1).card = 3360 ∧
    (sector (Fin 4 × Fin 4) 2 2 2).card = 120 ∧
    (sector (Fin 5 × Fin 5) 2 1 0).card = 6900 ∧
    (sector (Fin 5 × Fin 5) 2 1 1).card = 600

/-- **Average hop count on any finite simple graph.** For `2 ≤ N` and `n ≤ N`, the number
of hops `M(S)`, averaged over the `C(N, n)` configurations of `n` particles, is
`2|E| · n(N - n)/(N(N - 1))`. -/
def HopAverage : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ),
    n ≤ Fintype.card V → 2 ≤ Fintype.card V →
      ((∑ S ∈ powersetCard n (univ : Finset V), (hops G S).card : ℕ) : ℚ) /
          (Fintype.card V).choose n =
        2 * G.edgeFinset.card * n * (Fintype.card V - n) /
          (Fintype.card V * (Fintype.card V - 1))

/-- **Average hop count on a `z`-regular graph:** `n z (N - n)/(N - 1)`. -/
def HopAverageRegular : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (z n : ℕ), G.IsRegularOfDegree z → n ≤ Fintype.card V → 2 ≤ Fintype.card V →
      ((∑ S ∈ powersetCard n (univ : Finset V), (hops G S).card : ℕ) : ℚ) /
          (Fintype.card V).choose n =
        n * z * (Fintype.card V - n) / (Fintype.card V - 1)

/-- **Average hop count on the `L × L` torus:** for `L ≥ 3` and `n ≤ L²`, it is
`4n(L² - n)/(L² - 1)`. -/
def HopAverageTorus : Prop :=
  ∀ L n : ℕ, 3 ≤ L → n ≤ L * L →
    ((∑ S ∈ powersetCard n (univ : Finset (Fin L × Fin L)), (hops (torus L) S).card : ℕ) :
        ℚ) / (L * L).choose n =
      4 * n * (L * L - n) / (L * L - 1)

/-- **The torus values at `n = 4`:** the average hop count is `64/5 = 12.8` for `L = 4` and
`14` for `L = 5`. At `λ = 1` these are the values of `μ₂(U → ∞)` printed by the
sparse-trace code. -/
def HopAverageTorusValues : Prop :=
  ((∑ S ∈ powersetCard 4 (univ : Finset (Fin 4 × Fin 4)), (hops (torus 4) S).card : ℕ) :
      ℚ) / (4 * 4).choose 4 = 64 / 5 ∧
    ((∑ S ∈ powersetCard 4 (univ : Finset (Fin 5 × Fin 5)), (hops (torus 5) S).card : ℕ) :
      ℚ) / (5 * 5).choose 4 = 14

/-- **A projected hopping operator has zero diagonal**, so its trace on any basis vanishes:
a hop always changes the configuration. -/
def ProjectedHoppingDiagonalZero : Prop :=
  ∀ (V σ : Type) [DecidableEq V] (G : SimpleGraph V) (t : ℝ)
    (H : Matrix (Config V σ) (Config V σ) ℂ), IsProjectedHopping G t H → ∀ c, H c c = 0

/-- **The diagonal of `H²`.** At every configuration `c` of the basis `B`, the diagonal
element of `H²` computed in `B` is `t² M(c)`, where `M(c)` is the number of hops out of
`c`. -/
def ProjectedHoppingSquareDiagonal : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (H : Matrix (Config V σ) (Config V σ) ℂ)
    (n : σ → ℕ), IsProjectedHopping G t H → ∀ c ∈ basis V n,
      ∑ b ∈ basis V n, H c b * H b c = (t : ℂ) ^ 2 * (hops G (occ c)).card

/-- **The exact second-moment theorem.** On a finite simple graph with `N ≥ 2` vertices and
`|E|` edges, the second spectral moment of a projected hopping operator with hopping modulus
`t`, on the (nonempty) no-double-occupancy basis with `n_s` particles of spin `s`, is
`μ₂ = t² · 2|E| · n(N - n)/(N(N - 1))` with `n = ∑ n_s`. It depends on the spin
composition only through `n`. -/
def SecondMomentTheorem : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (H : Matrix (Config V σ) (Config V σ) ℂ)
    (n : σ → ℕ), IsProjectedHopping G t H → (basis V n).Nonempty → 2 ≤ Fintype.card V →
      secondMoment (basis V n) H =
        (t : ℂ) ^ 2 * (2 * G.edgeFinset.card) * (∑ s, n s : ℕ) *
            ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
          ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1))

/-- **The exact second-moment theorem on a `z`-regular graph:**
`μ₂ = t² n z (N - n)/(N - 1)`. -/
def SecondMomentRegular : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (H : Matrix (Config V σ) (Config V σ) ℂ)
    (z : ℕ) (n : σ → ℕ), IsProjectedHopping G t H → G.IsRegularOfDegree z →
      (basis V n).Nonempty → 2 ≤ Fintype.card V →
        secondMoment (basis V n) H =
          (t : ℂ) ^ 2 * (∑ s, n s : ℕ) * z * ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
            ((Fintype.card V : ℂ) - 1)

/-- **The exact second-moment theorem on the `L × L` torus** (`L ≥ 3`):
`μ₂ = t² · 4n(L² - n)/(L² - 1)`. -/
def SecondMomentTorus : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (L : ℕ) (t : ℝ)
    (H : Matrix (Config (Fin L × Fin L) σ) (Config (Fin L × Fin L) σ) ℂ) (n : σ → ℕ),
    3 ≤ L → IsProjectedHopping (torus L) t H → (basis (Fin L × Fin L) n).Nonempty →
      secondMoment (basis (Fin L × Fin L) n) H =
        (t : ℂ) ^ 2 * 4 * (∑ s, n s : ℕ) * ((L : ℂ) * L - (∑ s, n s : ℕ)) /
          ((L : ℂ) * L - 1)

/-- **The hypotheses can be met.** On every graph and for every `t ≥ 0` some operator is a
projected hopping operator (for example the hop matrix with every sign `+`, i.e. hard-core
bosons). The claims about projected hopping operators are therefore not vacuous. -/
def ProjectedHoppingExists : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℝ), 0 ≤ t → ∃ H : Matrix (Config V σ) (Config V σ) ℂ, IsProjectedHopping G t H

/-- **The two-electron model is Hermitian** for antisymmetric Peierls phases,
`A(x, y) = -A(y, x)`: a check that `pairHopping` is the intended operator. -/
def PairHoppingHermitian : Prop :=
  ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ), (∀ x y, A y x = -A x y) → (pairHopping G t A).IsHermitian

/-- **No single hop connects two doublons**, so the first-order term of the effective
Hamiltonian on the doublon states vanishes. -/
def DoublonFirstOrderZero : Prop :=
  ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) (R' R : V), pairHopping G t A (R', R') (R, R) = 0

/-- **The doubled Peierls phase.** For adjacent sites `R`, `R'`, the second-order amplitude
for a doublon to hop from `R` to `R'` is `t_d e^{2 i A(R', R)}`, `t_d = 2t²/U`: twice the
phase `A(R', R)` of a single electron on that bond. -/
def DoubledPeierlsPhase : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) (U : ℝ) (R R' : V), G.Adj R R' →
      doublonSecondOrder (pairHopping G t A) U R' R =
        2 * (t : ℂ) ^ 2 / U * Complex.exp (2 * A R' R * Complex.I)

/-- **The doublon hops only to nearest neighbours** at second order. -/
def DoublonHoppingRange : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) (U : ℝ) (R R' : V), R ≠ R' → ¬ G.Adj R R' →
      doublonSecondOrder (pairHopping G t A) U R' R = 0

/-- **The on-site shift does not depend on the phases.** For antisymmetric `A`, the
second-order energy shift of a doublon on `R` is `2 z t²/U`, `z` the degree of `R`. -/
def DoublonOnSiteShift : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) (U : ℝ) (R : V), (∀ x y, A y x = -A x y) →
      doublonSecondOrder (pairHopping G t A) U R R = 2 * G.degree R * (t : ℂ) ^ 2 / U

/-- **The on-site shift on the `L × L` torus** (`L ≥ 3`): `8 t²/U`. -/
def DoublonOnSiteShiftTorus : Prop :=
  ∀ (L : ℕ) (t : ℝ) (A : Fin L × Fin L → Fin L × Fin L → ℝ) (U : ℝ) (R : Fin L × Fin L),
    3 ≤ L → (∀ x y, A y x = -A x y) →
      doublonSecondOrder (pairHopping (torus L) t A) U R R = 8 * (t : ℂ) ^ 2 / U

/-- **Triangles of the torus.** The `L × L` torus has no triangle exactly when `L ≠ 3`. -/
def TorusTriangleFree : Prop :=
  ∀ L : ℕ, (torus L).CliqueFree 3 ↔ L ≠ 3

/-- **The Schrieffer–Wolff cross term vanishes on triangle-free graphs.** Let `H` be a hopping
operator, `B` a set of states without doubly occupied sites (`P₀`, or one particle-number
sector of it) and `Q` a set of states with a doubly occupied site (`Q₁`). With
`T₀ = P₀ H P₀` and `V = T₁† T₁` (`virtualOp`), `Tr(T₀ V) = ∑_{a, b ∈ B} H_{ab} V_{ba} = 0`, so
`⟨T₀, V⟩_HS = 0`. -/
def SchriefferWolffCrossTerm : Prop :=
  ∀ (V σ : Type) [DecidableEq V] [DecidableEq σ] (G : SimpleGraph V)
    (H : Matrix (FockState V σ) (FockState V σ) ℂ) (B Q : Finset (FockState V σ)),
    IsHoppingOperator G H → G.CliqueFree 3 → (∀ a ∈ B, ∀ v, siteOcc a v ≤ 1) →
      (∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) → ∑ a ∈ B, ∑ b ∈ B, H a b * virtualOp Q H b a = 0

/-- **No `1/U` correction to the second moment on triangle-free graphs.** With `H`, `B`, `Q`
as above, the second moment on `B` of the second-order effective Hamiltonian `T₀ - V/U` is
`μ₂(T₀) + Var(V)/U²`, where `μ₂(T₀) = secondMoment B H` and `Var(V) = secondMoment B V`. -/
def SchriefferWolffSecondMoment : Prop :=
  ∀ (V σ : Type) [DecidableEq V] [DecidableEq σ] (G : SimpleGraph V)
    (H : Matrix (FockState V σ) (FockState V σ) ℂ) (B Q : Finset (FockState V σ)) (U : ℝ),
    IsHoppingOperator G H → G.CliqueFree 3 → (∀ a ∈ B, ∀ v, siteOcc a v ≤ 1) →
      (∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) →
        secondMoment B (H - (U : ℂ)⁻¹ • virtualOp Q H) =
          secondMoment B H + secondMoment B (virtualOp Q H) / (U : ℂ) ^ 2

/-- **The same on the `L × L` torus, `L ≥ 4`.** -/
def SchriefferWolffSecondMomentTorus : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (L : ℕ)
    (H : Matrix (FockState (Fin L × Fin L) σ) (FockState (Fin L × Fin L) σ) ℂ)
    (B Q : Finset (FockState (Fin L × Fin L) σ)) (U : ℝ),
    4 ≤ L → IsHoppingOperator (torus L) H → (∀ a ∈ B, ∀ v, siteOcc a v ≤ 1) →
      (∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) →
        secondMoment B (H - (U : ℂ)⁻¹ • virtualOp Q H) =
          secondMoment B H + secondMoment B (virtualOp Q H) / (U : ℂ) ^ 2

/-- **The triangle-free hypothesis cannot be dropped.** On the `3 × 3` torus there are a
Hermitian hopping operator `H`, a set `B` of states without double occupancy and a set `Q`
of states with one such that `∑_{a, b ∈ B} H_{ab} V_{ba} ≠ 0`. -/
def CrossTermNeedsTriangleFree : Prop :=
  ∃ (H : Matrix (FockState (Fin 3 × Fin 3) (Fin 2)) (FockState (Fin 3 × Fin 3) (Fin 2)) ℂ)
    (B Q : Finset (FockState (Fin 3 × Fin 3) (Fin 2))),
    H.IsHermitian ∧ IsHoppingOperator (torus 3) H ∧ (∀ a ∈ B, ∀ v, siteOcc a v ≤ 1) ∧
      (∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) ∧ ∑ a ∈ B, ∑ b ∈ B, H a b * virtualOp Q H b a ≠ 0

/-- **The mean of a sample drawn without replacement** from a centred population (`∑ ε = 0`)
is `0`. -/
def SampleMean : Prop :=
  ∀ (V : Type) [Fintype V] (ε : V → ℝ) (k : ℕ),
    ∑ v, ε v = 0 → sampleMoment ε k 1 = 0

/-- **The finite-population correction.** Drawing `k ≤ N` of `N ≥ 2` values without
replacement from a centred population with `σ₁² = P₂/N`, the variance of the sum is
`k σ₁² (N - k)/(N - 1)`. -/
def FinitePopulationVariance : Prop :=
  ∀ (V : Type) [Fintype V] (ε : V → ℝ) (k : ℕ),
    ∑ v, ε v = 0 → k ≤ Fintype.card V → 2 ≤ Fintype.card V →
      sampleMoment ε k 2 = k * ((∑ i, ε i ^ 2) / Fintype.card V) * (Fintype.card V - k) /
        (Fintype.card V - 1)

/-- **The finite-population fourth moment** (App. B). With `P₂ = ∑ ε²`, `P₄ = ∑ ε⁴` and
`p_m = k(k-1)⋯(k-m+1)/(N(N-1)⋯(N-m+1))`,
`μ₄ = P₄ (p₁ - 7p₂ + 12p₃ - 6p₄) + 3 P₂² (p₂ - 2p₃ + p₄)` for every `k ≤ N`. -/
def FinitePopulationFourthMoment : Prop :=
  ∀ (V : Type) [Fintype V] (ε : V → ℝ) (k : ℕ),
    ∑ v, ε v = 0 → k ≤ Fintype.card V →
      sampleMoment ε k 4 =
        (∑ i, ε i ^ 4) * (inclusionProb (Fintype.card V) k 1 -
          7 * inclusionProb (Fintype.card V) k 2 + 12 * inclusionProb (Fintype.card V) k 3 -
            6 * inclusionProb (Fintype.card V) k 4) +
        3 * (∑ i, ε i ^ 2) ^ 2 * (inclusionProb (Fintype.card V) k 2 -
          2 * inclusionProb (Fintype.card V) k 3 + inclusionProb (Fintype.card V) k 4)

/-- **Second moments of independent variables add** when one has mean `0`: for `f` on `A`
and `g` on `B`, uniformly and independently distributed, `E[(f + g)²] = E[f²] + E[g²]`. -/
def IndependentSumSecondMoment : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (f : A → ℝ) (g : B → ℝ),
    ∑ b, g b = 0 →
      (∑ a, ∑ b, (f a + g b) ^ 2) / (Fintype.card A * Fintype.card B) =
        (∑ a, f a ^ 2) / Fintype.card A + (∑ b, g b ^ 2) / Fintype.card B

/-- **Fourth moments of independent zero-mean variables** (App. B):
`μ₄(f + g) = μ₄(f) + μ₄(g) + 6 Var f Var g`. -/
def IndependentSumFourthMoment : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (f : A → ℝ) (g : B → ℝ),
    ∑ a, f a = 0 → ∑ b, g b = 0 →
      (∑ a, ∑ b, (f a + g b) ^ 4) / (Fintype.card A * Fintype.card B) =
        (∑ a, f a ^ 4) / Fintype.card A + (∑ b, g b ^ 4) / Fintype.card B +
          6 * ((∑ a, f a ^ 2) / Fintype.card A) * ((∑ b, g b ^ 2) / Fintype.card B)

/-- **The torus band** `ε(q) = -2t (cos q₁ + cos q₂)`, `L ≥ 3`: it is centred, and
`∑ ε² = 4t² L²`, so `σ₁² = 4t² = z t²`. -/
def TorusBandMoments : Prop :=
  ∀ (L : ℕ) (t : ℝ), 3 ≤ L →
    ∑ q, torusBand L t q = 0 ∧ ∑ q, torusBand L t q ^ 2 = 4 * t ^ 2 * L ^ 2

/-- **`μ₂` of free fermions of one species on the torus** (§5.3): `n ≤ L²` particles on the
`L × L` torus, `L ≥ 3`, have `μ₂ = t² · 4n(L² - n)/(L² - 1)`. -/
def FreeFermionSecondMomentTorus : Prop :=
  ∀ (L n : ℕ) (t : ℝ), 3 ≤ L → n ≤ L * L →
    sampleMoment (torusBand L t) n 2 = t ^ 2 * 4 * n * (L * L - n) / (L * L - 1)

/-- **For one spin species the `U = 0` and `U = ∞` second moments coincide**: the
momentum-space value (sampling without replacement from the band) equals the real-space
value (`SecondMomentTorus`) for every projected hopping operator. -/
def FreeAndProjectedSecondMomentsAgree : Prop :=
  ∀ (L : ℕ) (t : ℝ) (H : Matrix (Config (Fin L × Fin L) Unit) (Config (Fin L × Fin L) Unit) ℂ)
    (n : ℕ), 3 ≤ L → IsProjectedHopping (torus L) t H → n ≤ L * L →
      (basis (Fin L × Fin L) (fun _ : Unit => n)).Nonempty →
        (sampleMoment (torusBand L t) n 2 : ℂ) =
          secondMoment (basis (Fin L × Fin L) (fun _ : Unit => n)) H

/-- **The finite-population table** (`L = 4`, `t = 1`, one species): `μ₂` and `μ₄` are
`112/15` and `2176/15` for `k = 2`, `52/5` and `9976/35` for `k = 3`, `64/5` and
`197632/455` for `k = 4`. -/
def FinitePopulationTable : Prop :=
  sampleMoment (torusBand 4 1) 2 2 = 112 / 15 ∧ sampleMoment (torusBand 4 1) 2 4 = 2176 / 15 ∧
    sampleMoment (torusBand 4 1) 3 2 = 52 / 5 ∧ sampleMoment (torusBand 4 1) 3 4 = 9976 / 35 ∧
    sampleMoment (torusBand 4 1) 4 2 = 64 / 5 ∧ sampleMoment (torusBand 4 1) 4 4 = 197632 / 455

/-- **Closed walks move few particles.** On any graph, `h` hops of hard-core particles that
start on distinct sites and end with the particles permuted by `σ` (the particle `p` ends
where the particle `σ p` started) move no particle (`σ = 1`) or fewer than `h` of them. -/
def ClosedWalkFewMoved : Prop :=
  ∀ (P V : Type) [Fintype P] [DecidableEq P] (G : SimpleGraph V)
    (walk : ℕ → P → V) (h : ℕ) (σ : Equiv.Perm P), Function.Injective (walk 0) →
      (∀ i < h, IsParticleHop G (walk i) (walk (i + 1))) → (∀ p, walk h p = walk 0 (σ p)) →
        σ ≠ 1 → σ.support.card < h

/-- **Four-hop closed walks** (§6, App. C): on any graph they induce the identity, a
transposition or a 3-cycle, never a 4-cycle or a double transposition. -/
def FourHopPermutations : Prop :=
  ∀ (P V : Type) [Fintype P] [DecidableEq P] (G : SimpleGraph V)
    (walk : ℕ → P → V) (σ : Equiv.Perm P), Function.Injective (walk 0) →
      (∀ i < 4, IsParticleHop G (walk i) (walk (i + 1))) → (∀ p, walk 4 p = walk 0 (σ p)) →
        σ = 1 ∨ σ.IsSwap ∨ σ.IsThreeCycle

/-- **Both nontrivial cases occur.** On every `L × L` torus with `L ≥ 3`, a four-hop closed
walk of two particles induces a transposition (ring exchange), and one of three particles
induces a 3-cycle. -/
def FourHopExchangesOccur : Prop :=
  ∀ L : ℕ, 3 ≤ L →
    (∃ (walk : ℕ → Fin 2 → Fin L × Fin L) (σ : Equiv.Perm (Fin 2)),
      Function.Injective (walk 0) ∧ (∀ i < 4, IsParticleHop (torus L) (walk i) (walk (i + 1))) ∧
        (∀ p, walk 4 p = walk 0 (σ p)) ∧ σ.IsSwap) ∧
    (∃ (walk : ℕ → Fin 3 → Fin L × Fin L) (σ : Equiv.Perm (Fin 3)),
      Function.Injective (walk 0) ∧ (∀ i < 4, IsParticleHop (torus L) (walk i) (walk (i + 1))) ∧
        (∀ p, walk 4 p = walk 0 (σ p)) ∧ σ.IsThreeCycle)

/-- **The 3-cycle count is affine in the same-spin pair count** (§6). With `N↑ = a`,
`N↓ = b`, `n = a + b` and `P_same = C(a, 2) + C(b, 2)`,
`C(a, 3) + C(b, 3) = C(n, 3) - (n - 2)/2 · (C(n, 2) - P_same)`. -/
def ThreeCycleCountAffine : Prop :=
  ∀ a b : ℕ, ((a.choose 3 + b.choose 3 : ℕ) : ℚ) = (a + b).choose 3 -
    ((a + b : ℚ) - 2) / 2 * ((a + b).choose 2 - (a.choose 2 + b.choose 2 : ℕ))

/-- **The sorted-tuple sign rule** (App. E): `c†_{o'} c_o |S⟩ = (-1)^{m + p} |S \ {o} ∪ {o'}⟩`
when `o ∈ S` and `o' ∉ S \ {o}`, with `m` the number of orbitals of `S` before `o` and `p` the
number of orbitals of `S \ {o}` before `o'`; otherwise `0`. -/
def SortedTupleSignRule : Prop :=
  ∀ (O : Type) [Fintype O] [DecidableEq O] (ord : O ↪ ℕ) (o o' : O) (S' S : Finset O),
    (create ord o' * annihilate ord o) S' S =
      if o ∈ S ∧ o' ∉ S.erase o ∧ S' = insert o' (S.erase o) then
        (-1) ^ (countBelow ord S o + countBelow ord (S.erase o) o') else 0

/-- **The Hubbard hopping term is Hermitian** for antisymmetric Peierls phases. -/
def HubbardHoppingHermitian : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℝ) (A : V → V → ℝ) (ord : V × σ ↪ ℕ),
    (∀ x y, A y x = -A x y) → (hubbardHopping G t A ord).IsHermitian

/-- **The Hubbard hopping term connects only Fock states one hop apart.** -/
def HubbardHoppingIsHoppingOperator : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℝ) (A : V → V → ℝ) (ord : V × σ ↪ ℕ),
    IsHoppingOperator G (hubbardHopping G t A ord)

/-- **`H∞` built from fermion operators is a projected hopping operator.** For `t ≥ 0`,
antisymmetric Peierls phases and any ordering of the orbitals, `H∞ = P₀ H_t P₀` in the
configuration basis has the three properties of `IsProjectedHopping`. -/
def ProjectedHubbardIsProjectedHopping : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℝ) (A : V → V → ℝ) (ord : V × σ ↪ ℕ),
    0 ≤ t → (∀ x y, A y x = -A x y) → IsProjectedHopping G t (projectedHubbard G t A ord)

/-- **The exact second-moment theorem for `H∞` itself** (§5.2): on a finite simple graph with
`N ≥ 2` vertices, `μ₂ = t² · 2|E| · n(N - n)/(N(N - 1))` on the no-double-occupancy basis with
`n_s` particles of spin `s`, `n = ∑ n_s`, for any Peierls phases and any sign convention. -/
def SecondMomentHubbard : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℝ) (A : V → V → ℝ) (ord : V × σ ↪ ℕ) (n : σ → ℕ),
    0 ≤ t → (∀ x y, A y x = -A x y) → (basis V n).Nonempty → 2 ≤ Fintype.card V →
      secondMoment (basis V n) (projectedHubbard G t A ord) =
        (t : ℂ) ^ 2 * (2 * G.edgeFinset.card) * (∑ s, n s : ℕ) *
            ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
          ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1))

/-- **The second moment of `H∞` on the `L × L` torus** (`L ≥ 3`):
`μ₂ = t² · 4n(L² - n)/(L² - 1)`. -/
def SecondMomentHubbardTorus : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (L : ℕ) (t : ℝ)
    (A : Fin L × Fin L → Fin L × Fin L → ℝ) (ord : (Fin L × Fin L) × σ ↪ ℕ) (n : σ → ℕ),
    3 ≤ L → 0 ≤ t → (∀ x y, A y x = -A x y) → (basis (Fin L × Fin L) n).Nonempty →
      secondMoment (basis (Fin L × Fin L) n) (projectedHubbard (torus L) t A ord) =
        (t : ℂ) ^ 2 * 4 * (∑ s, n s : ℕ) * ((L : ℂ) * L - (∑ s, n s : ℕ)) / ((L : ℂ) * L - 1)

/-- **No `1/U` correction for the Hubbard hopping term on triangle-free graphs** (§7.2):
`μ₂(T₀ - V/U) = μ₂(T₀) + Var(V)/U²` with `T₀`, `V` built from `H_t` itself. -/
def SchriefferWolffHubbard : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℝ) (A : V → V → ℝ) (ord : V × σ ↪ ℕ)
    (B Q : Finset (FockState V σ)) (U : ℝ),
    G.CliqueFree 3 → (∀ a ∈ B, ∀ v, siteOcc a v ≤ 1) → (∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) →
      secondMoment B (hubbardHopping G t A ord -
          (U : ℂ)⁻¹ • virtualOp Q (hubbardHopping G t A ord)) =
        secondMoment B (hubbardHopping G t A ord) +
          secondMoment B (virtualOp Q (hubbardHopping G t A ord)) / (U : ℂ) ^ 2

/-- **The exact second-moment theorem for bond-dependent moduli.** For every operator with
the properties of `IsWeightedProjectedHopping w`, on the nonempty no-double-occupancy basis
with `n = ∑ n_s` particles and `N ≥ 2` sites,
`μ₂ = n(N - n)/(N(N - 1)) · ∑_{i ≠ j} w(i, j)²`. -/
def SecondMomentWeightedTheorem : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] (w : V → V → ℝ)
    (H : Matrix (Config V σ) (Config V σ) ℂ) (n : σ → ℕ),
    IsWeightedProjectedHopping w H → (basis V n).Nonempty → 2 ≤ Fintype.card V →
      secondMoment (basis V n) H =
        (∑ s, n s : ℕ) * ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
            ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, ((w i j : ℝ) : ℂ) ^ 2

/-- **The paper's second-moment formula for `H∞` with arbitrary amplitudes** (abstract,
§5.2). With `H_t = -∑_{i ≠ j, s} t_ij c†_{is} c_{js}` built from fermion operators,
`t_ji = conj(t_ij)`, and `H∞ = P₀ H_t P₀`:
`μ₂ = n(N - n)/(N(N - 1)) · ∑_{i ≠ j} |t_ij|²`, for any spin composition and any ordering of
the orbitals. -/
def SecondMomentHubbardWeighted : Prop :=
  ∀ (V σ : Type) [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] (tt : V → V → ℂ)
    (ord : V × σ ↪ ℕ) (n : σ → ℕ),
    (∀ i j, tt j i = star (tt i j)) → (basis V n).Nonempty → 2 ≤ Fintype.card V →
      secondMoment (basis V n) (projectedHubbardWeighted tt ord) =
        (∑ s, n s : ℕ) * ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
            ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, ((‖tt i j‖ : ℝ) : ℂ) ^ 2

end HubbardMoments.Spec
