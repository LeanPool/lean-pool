/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Defs
public import LeanPool.HubbardMoments.Peierls

/-! # Hubbard hopping operators with Peierls phases -/

@[expose] public section

namespace HubbardMoments

section PairHopping

variable {V : Type*} [DecidableEq V]

/-- **Two electrons of opposite spin, with Peierls phases.** The basis state `(i, j)` is
`c†_{i↑} c†_{j↓} |0⟩`; `(R, R)` is the doublon `D_R` on site `R`. The hopping operator
`H_t(A) = -t ∑_{x ~ y, s} e^{i A(y, x)} c†_{y s} c_{x s}` moves one electron from a site `x`
to an adjacent site `y` with amplitude `-t e^{i A(y, x)}`: `A y x` is the phase of the hop
`x → y`. With one electron of each spin no fermionic sign arises, so these are all the
matrix elements. -/
noncomputable def pairHopping (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) : Matrix (V × V) (V × V) ℂ := fun p q =>
  (if p.2 = q.2 ∧ G.Adj q.1 p.1 then peierlsAmplitude t (A p.1 q.1) else 0) +
    (if p.1 = q.1 ∧ G.Adj q.2 p.2 then peierlsAmplitude t (A p.2 q.2) else 0)

end PairHopping

section Spin

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]

/-- **The Hubbard hopping term with Peierls phases**, built from fermion operators on the
orbitals `(site, spin)` ordered by `ord`:
`H_t = -t ∑_{x ~ y} ∑_s e^{i A(y, x)} c†_{y s} c_{x s}`, the sum over ordered pairs of
adjacent sites (`arcs G`). It is Hermitian when `A` is antisymmetric. -/
noncomputable def hubbardHopping (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) (ord : V × σ ↪ ℕ) : Matrix (FockState V σ) (FockState V σ) ℂ :=
  fermionHopping G (fun i j => peierlsAmplitude t (A j i)) ord

/-- **The projected hopping operator `H∞ = P₀ H_t P₀`** of the `U → ∞` Hubbard model, in the
configuration basis. The configurations are exactly the Fock states without double
occupancy (`configState` is injective with that image), so the block of `H_t` on them is
`c, b ↦ (H_t)_{configState c, configState b}`. -/
noncomputable def projectedHubbard (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) (ord : V × σ ↪ ℕ) : Matrix (Config V σ) (Config V σ) ℂ :=
  projectedFermionHopping G (fun i j => peierlsAmplitude t (A j i)) ord

end Spin

end HubbardMoments
