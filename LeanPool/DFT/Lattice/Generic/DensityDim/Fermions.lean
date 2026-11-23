/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Generic.DensityDim
public import LeanPool.DFT.Lattice.GenericHK

/-!
# Non-uv densities of spinless lattice fermions have codimension at least two

`dimH_nonUVDens_lattice_fermions_w`: for `N` spinless fermions (`0 < N < M`) on a connected graph
with symmetric hopping amplitudes of a common sign and any density–density interaction, the
densities of non-degenerate ground states that are shared with a potential differing by more than
a constant form a set of Hausdorff dimension at most `M - 3`, i.e. of codimension at least two in
the `(M-1)`-dimensional space of densities. `dimH_nonUVDens_lattice_fermions`: the same for
uniform hopping `t ≠ 0`. The `Nonempty` variants give the form `dimH + 3 ≤ M`.
-/

@[expose] public section

namespace DFT

open MvPolynomial

variable {M N : ℕ}

/-- The Krylov polynomials of the lattice fermion Hamiltonian, multiplied over configurations:
a nonzero polynomial vanishing at every non-uniquely-v-representable potential. -/
theorem exists_poly_lattice_fermions_w {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M)
    (Vint : Conf M N → ℝ) :
    ∃ P : MvPolynomial (Fin M) ℝ, P ≠ 0 ∧
      ∀ v, NonUV (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ) v → eval v P = 0 :=
  exists_krylov_certificate (Tr := constPot) (H0Fw_isSymm G htsym Vint) (rigid_occF hN0 hNM)
    (fun j => (Fintype.equivFin (Conf M N) j : ℕ))
    (fun c => hstar_lattice_fermions_w hG hts c Vint)


/-- **Non-uv densities of lattice fermions, edge-dependent hopping.** For `N` spinless fermions
(`0 < N < M`) on a connected graph with symmetric hopping amplitudes of a common sign and any
density–density interaction, the densities of non-degenerate ground states shared with a
potential differing by more than a constant have Hausdorff dimension at most `M - 3`. -/
theorem dimH_nonUVDens_lattice_fermions_w {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M)
    (Vint : Conf M N → ℝ) :
    dimH (NonUVDens (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ)) ≤ (M : ENNReal) - 3 := by
  obtain ⟨P, hP, hPZ⟩ := exists_poly_lattice_fermions_w hG htsym hts hN0 hNM Vint
  simpa using dimH_nonUVDens_le (H0Fw_isSymm G htsym Vint) ⟨N, sum_occF⟩ hP hPZ

/-- `dimH_nonUVDens_lattice_fermions_w` in the form `dimH + 3 ≤ M` (when there are non-uv
densities at all; in particular they exist only for `M ≥ 3`). -/
theorem dimH_nonUVDens_lattice_fermions_w' {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M)
    (Vint : Conf M N → ℝ)
    (hne : (NonUVDens (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ)).Nonempty) :
    dimH (NonUVDens (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ)) + 3 ≤ M := by
  obtain ⟨P, hP, hPZ⟩ := exists_poly_lattice_fermions_w hG htsym hts hN0 hNM Vint
  simpa using dimH_nonUVDens (H0Fw_isSymm G htsym Vint) ⟨N, sum_occF⟩ hP hPZ hne

/-- **Non-uv densities of lattice fermions.** For `N` spinless fermions (`0 < N < M`) on a
connected graph with hopping `t ≠ 0` and any density–density interaction, the densities of
non-degenerate ground states shared with a potential differing by more than a constant have
Hausdorff dimension at most `M - 3`. -/
theorem dimH_nonUVDens_lattice_fermions {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : ℝ} (ht : t ≠ 0) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    dimH (NonUVDens (H0F G t Vint) (occF : Fin M → Conf M N → ℝ)) ≤ (M : ENNReal) - 3 := by
  rw [H0F_eq_H0Fw]
  exact dimH_nonUVDens_lattice_fermions_w hG (fun _ _ => rfl) (s := t)
    (fun _ _ _ => mul_self_pos.mpr ht) hN0 hNM Vint

/-- `dimH_nonUVDens_lattice_fermions` in the form `dimH + 3 ≤ M`. -/
theorem dimH_nonUVDens_lattice_fermions' {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : ℝ} (ht : t ≠ 0) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ)
    (hne : (NonUVDens (H0F G t Vint) (occF : Fin M → Conf M N → ℝ)).Nonempty) :
    dimH (NonUVDens (H0F G t Vint) (occF : Fin M → Conf M N → ℝ)) + 3 ≤ M := by
  rw [H0F_eq_H0Fw] at hne ⊢
  exact dimH_nonUVDens_lattice_fermions_w' hG (fun _ _ => rfl) (s := t)
    (fun _ _ _ => mul_self_pos.mpr ht) hN0 hNM Vint hne

end DFT
