/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RegularPatchNeighborhood

/-!
# The local statement (LS) for analytic subsets

Blueprint `lag:local-statement` (Demailly, *Complex analytic and differential geometry*,
II.4.24, II.4.26, II.5.3).

Near every point `p` of an analytic subset `A` of a complex manifold there are an open
neighbourhood `W` of `p` inside the preferred chart at `p` and finitely many subsets
`A₁, …, A_r` of `W` with `A ∩ W = ⋃ Aᵢ` such that

* each `Aᵢ` is the common zero set in `W` of finitely many functions holomorphic on the
  chart image of `W`;
* EVERY regular point of `Aᵢ` has dimension `dᵢ`, and the regular points of `Aᵢ` of
  dimension `dᵢ` are dense in `Aᵢ`;
* for `i ≠ l`, `Aᵢ ∩ A_l` has empty interior relative to `Aᵢ`.

The `Aᵢ` are representatives of the irreducible components of the germ of `A` at `p`; the
statement is the output of the local parametrization theorem for irreducible germs
(blueprint `lag:irreducible-germ-pure`, `lag:thin-subgerm`).

`LocalDecomposition A p` bundles these data.  Their existence,
`exists_localDecomposition`, is assembled in `Pending.LocalStatementAssembly`; the global
consequences (analyticity of the dimension strata and pure dimensionality of irreducible
analytic sets) are derived from it in `Pending.PureDimension`.
-/

@[expose] public section

open Set

namespace SGPT.Foundations.Analysis.Pending.AnalyticLocalStatement

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Local decomposition data (LS)** for `A` at `p`: finitely many analytic pieces of a
neighbourhood of `p`, each pure-dimensional, pairwise meeting in relatively thin sets. -/
structure LocalDecomposition (A : Set M) (p : M) where
  /-- The neighbourhood of `p` on which the decomposition holds. -/
  nbhd : Set M
  isOpen_nbhd : IsOpen nbhd
  mem_nbhd : p ∈ nbhd
  nbhd_subset_source : nbhd ⊆ (complexChartAt (n := n) p).val.source
  /-- The number of pieces. -/
  count : ℕ
  /-- The pieces `Aᵢ`. -/
  piece : Fin count → Set M
  /-- The dimension `dᵢ` of the piece `Aᵢ`. -/
  dim : Fin count → ℕ
  /-- The number of equations of `Aᵢ`. -/
  eqnCount : Fin count → ℕ
  /-- The equations of `Aᵢ`, in the chart at `p`. -/
  eqn : (i : Fin count) → Fin (eqnCount i) → ComplexModel n → ℂ
  eqn_holomorphic : ∀ i j,
    DifferentiableOn ℂ (eqn i j) ((complexChartAt (n := n) p).val '' nbhd)
  piece_subset : ∀ i, piece i ⊆ nbhd
  mem_piece_iff : ∀ i, ∀ y ∈ nbhd,
    (y ∈ piece i ↔ ∀ j, eqn i j ((complexChartAt (n := n) p).val y) = 0)
  inter_nbhd_eq : A ∩ nbhd = ⋃ i, piece i
  /-- EVERY regular point of `Aᵢ` has dimension `dᵢ`. -/
  eq_dim_of_regularAtDim : ∀ i {y : M} {k : ℕ}, RegularAtDim (n := n) (piece i) y k → k = dim i
  /-- The regular points of `Aᵢ` of dimension `dᵢ` are dense in `Aᵢ`. -/
  subset_closure_regularLocus : ∀ i, piece i ⊆ closure (regularLocus (n := n) (piece i) (dim i))
  /-- `Aᵢ ∩ A_l` has empty interior relative to `Aᵢ` for `i ≠ l`. -/
  exists_mem_not_mem : ∀ i l, i ≠ l → ∀ O : Set M, IsOpen O → (O ∩ piece i).Nonempty →
    ∃ y ∈ O ∩ piece i, y ∉ piece l

end

end SGPT.Foundations.Analysis.Pending.AnalyticLocalStatement
