/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Scheme
public import LeanPool.FunctionSpaces.ApproximationSpaces.Error
public import LeanPool.FunctionSpaces.ApproximationSpaces.Instances.Span
public import LeanPool.FunctionSpaces.ApproximationSpaces.Instances.NTerm
public import LeanPool.FunctionSpaces.ApproximationSpaces.Instances.NTermHilbertBasis
public import LeanPool.FunctionSpaces.ApproximationSpaces.Norm
public import LeanPool.FunctionSpaces.ApproximationSpaces.Dyadic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Space
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Lq
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Dyadic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Rearrangement
public import LeanPool.FunctionSpaces.ApproximationSpaces.Embedding
public import LeanPool.FunctionSpaces.ApproximationSpaces.Transfer
public import LeanPool.FunctionSpaces.ApproximationSpaces.Lift
public import LeanPool.FunctionSpaces.ApproximationSpaces.Nikolskii
public import LeanPool.FunctionSpaces.ApproximationSpaces.Jackson
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.KFunctional
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Representation
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.KMethod
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Couple
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Property
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Reiteration
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.ApproxSpaces
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.EFunctional
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.EFunctionalModuli
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Projection
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Blocks
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Synthesis
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Atomic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Trace
public import LeanPool.FunctionSpaces.ApproximationSpaces.Retract
public import LeanPool.FunctionSpaces.ApproximationSpaces.Moduli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Approximation spaces

This library is the abstract theory of approximation spaces in the sense of Pietsch
(J. Approx. Theory 32, 1981), together with real interpolation by the K-method.

**Approximation schemes.** An approximation scheme is an increasing sequence of sets
`A 0 ⊆ A 1 ⊆ A 2 ⊆ ⋯` in a real normed space `X`, with `A 0 = {0}`, `c • A n ⊆ A n` and
`A m + A n ⊆ A (m + n)`. The elements of `A n` are the approximants of complexity `n`:
polynomials of degree `< n`, combinations of the first `n` elements of a basis, or combinations
of at most `n` elements of a dictionary. The error of best approximation of `f ∈ X` from `A n` is

`E_n(f) = inf { ‖f - a‖ : a ∈ A n }`.

**Approximation spaces.** For a smoothness `s > 0` and a fine index `1 ≤ q ≤ ∞`, the space
`A^s_q` consists of the `f` whose errors decay at the rate `n^(-s)`, measured in `ℓ_q`:

`‖f‖_{A^s_q} = ‖(n^(s - 1/q) E_{n-1}(f))_{n ≥ 1}‖_{ℓ_q} < ∞`.

So smoothness becomes a rate of approximation. Two inequalities link the spaces `A^s_q` to
classical spaces such as Besov spaces. Jackson's inequality says that smooth elements are well
approximated. Bernstein's inequality says that approximants are smooth, with controlled norm.

**Real interpolation.** For a smaller space `Y` inside `X`, the K-functional
`K(t, f) = inf_y (‖f - y‖_X + t ‖y‖_Y)` measures how well `f` is approximated by elements of `Y`
of controlled size. The K-method builds from it the interpolation spaces `(X, Y)_{θ,q}`. Under
Jackson's and Bernstein's inequalities of order `r`, the representation theorem gives

`A^s_q = (X, Y)_{s/r,q}`   for `0 < s < r`.

Hence theorems about interpolation spaces, such as the reiteration theorem, apply to
approximation spaces.

**Setting.** Everything here is abstract. The schemes live in real normed spaces, and the
couples of the interpolation part live on additive commutative groups. No function spaces
occur, and the only measures are the counting measure behind the `ℓ_q` norms, Lebesgue measure on
`(0, ∞)` in the layer cake formula for sums, and `dt/t` on `(0, ∞)` in the continuous K-method.
One concrete scheme is treated here, since it needs only a Hilbert basis: best `n`-term
approximation, with the theorem of Stechkin and DeVore. The library `FunctionSpaces` applies the
theory to concrete schemes of functions.

## Layout

The files at the top level hold the schemes, the spaces `A^s_q` and the theorems about them. The
subfolders hold the basic examples of schemes (`Instances`), the sequence spaces
(`Sequences`), real interpolation (`Interpolation`) and decompositions (`Decompositions`). Names
below are relative to the namespace `ApproximationScheme`, except those that start with `ENNReal`,
`MeasureTheory`, `InterpCouple`, `HilbertBasis` or `lp`, and the decreasing rearrangement, which is
in the root namespace.

### The scheme and the error

* `ApproximationSpaces.Scheme`: the structure `ApproximationScheme` and its elementary
  consequences, the preimage `comap` and the image `map` of a scheme under a linear map, the
  scheme `ofSubmodules` of an increasing sequence of subspaces, and the dyadic scheme
  `ofMonotoneSubmodules`, with the `k`-th subspace at complexity `2^k`.
* `ApproximationSpaces.Error`: the error `E_n(f)`, `approxError`, with values in `ℝ≥0∞`, and
  its calculus: `E_0(f) = ‖f‖`, monotonicity in `n`, homogeneity, subadditivity, near-best
  approximants, the limit `E_n(f) → 0` exactly on the closure of `⋃ A n`
  (`tendsto_approxError_zero_iff`), the bound for linear maps (`approxError_map_le`), the
  extension of modulus bounds from a dense set (`approxError_le_of_dense`) and the Lebesgue
  inequality.

### Examples of schemes (`Instances/`)

* `ApproximationSpaces.Instances.Span`: linear approximation from the first `n` elements of a
  sequence, `ofSpan`. Its errors tend to zero exactly on the closed span.
* `ApproximationSpaces.Instances.NTerm`: nonlinear `n`-term approximation from a dictionary,
  `nTerm`. Its errors are at most those of `ofSpan` (`approxError_nTerm_le_ofSpan`).
* `ApproximationSpaces.Instances.NTermHilbertBasis`: best `n`-term approximation from a Hilbert
  basis of a complex Hilbert space, with the dictionary `HilbertBasis.coeffDictionary` of
  multiples of the basis vectors: the error as the smallest tail of the coefficients
  (`HilbertBasis.approxError_nTerm_sq_eq`), tail bounds by the rearranged coefficients, and
  the theorem of Stechkin and DeVore, `f ∈ A^(1/τ - 1/2)_τ` iff `(⟨e_i, f⟩)_i ∈ ℓ_τ` for
  `0 < τ < 2` (`HilbertBasis.memApprox_nTerm_iff`).

### The spaces `A^s_q` and their dyadic norm

* `ApproximationSpaces.Norm`: Pietsch's quasi-norm `approxNorm` of `A^s_q`, membership
  `MemApprox`, homogeneity, and the embedding `‖f‖ ≤ ‖f‖_{A^s_q}` for every `q ≠ 0`
  (`enorm_le_approxNorm`).
* `ApproximationSpaces.Dyadic`: the equivalent dyadic quasi-norm
  `‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}`, `approxNormDyadic`, the working norm of all later files;
  the equivalence holds for every `q ∈ (0, ∞]` (`memApprox_iff_approxNormDyadic_lt_top'`).
* `ApproximationSpaces.Space`: the quasi-triangle inequality and `A^s_q` as a submodule of `X`,
  `approxSpace`.

### Sequence spaces (`Sequences/`)

* `ApproximationSpaces.Sequences.Lq`: sums of powers in `[0, ∞]` (`ENNReal.rpow_tsum_le_tsum_rpow`),
  the `ℓ_q` norm `ENNReal.lqNorm` of a sequence in `ℝ≥0∞`, defined as the `L_q` norm for the
  counting measure, with its monotonicity in `q`, the quasi-triangle inequality for `q < 1`
  (`ENNReal.lqNorm_add_le'`), the Cauchy–Schwarz inequality, the dyadic weights
  `ENNReal.dyadicWeight`, powers of two and products in `[0, ∞]`, `L_q` norms of functions
  bounded on pieces, the subadditivity of `‖·‖_p^p` for `0 < p ≤ 1`
  (`MeasureTheory.eLpNorm_add_rpow_le_of_le_one`), and Parseval's identity for `ℓ²` in `ℝ≥0∞`
  (`lp.enorm_sq_eq_tsum`).
* `ApproximationSpaces.Sequences.Dyadic`: Cauchy condensation with power weights
  (`ENNReal.tsum_pow_mul_le_dyadic`) and for capped sequences (`ENNReal.tsum_min_le_dyadic`),
  three sums over dyadic scales, and the interpolation inequality for dyadic suprema
  (`ENNReal.tsum_dyadicWeight_mul_le_iSup`).
* `ApproximationSpaces.Sequences.Rearrangement`: the decreasing rearrangement
  `TauCeti.decreasingRearrangement` of a nonnegative null family (copied from TauCeti), the
  layer cake
  formula for sums, `∑_n (r*_n)^p = ∑_i r_i^p` (`tsum_ofReal_rpow_decreasingRearrangement`), and
  the block inequalities that compare `∑_i r_i^p` with `∑_l 2^l (r*_{2^l})^p`.
* `ApproximationSpaces.Sequences.Hardy`: the countable Minkowski inequality, window sums
  (`ENNReal.lqNorm_sum_Icc_le`), the two discrete Hardy inequalities (`ENNReal.hardy_sum_le`,
  `ENNReal.hardy_tail_le`), their forms for `0 < q ≤ 1` (`ENNReal.hardy_tail_le_of_le_one`) and
  for every exponent (`ENNReal.hardy_sum_le'`), powers inside an `ℓ_q` norm
  (`ENNReal.lqNorm_fun_rpow`, `ENNReal.lqNorm_div_fun_rpow`), almost diagonal sums and their
  constant `ENNReal.almostDiagonalConst`, shifts on `ℓ_q(ℤ)` and geometric convolutions.

### Embeddings, transfer and lifting

* `ApproximationSpaces.Embedding`: the embeddings `A^s_q ↪ A^s_r` for `q ≤ r` and
  `A^s_q ↪ A^t_r` for `t < s` (`MemApprox.mono`).
* `ApproximationSpaces.Transfer`: a bounded linear map `T` with `T (A n) ⊆ B n` maps `A^s_q(X)`
  into `B^s_q(Y)` with norm at most `‖T‖` (`approxNorm_map_le`).
* `ApproximationSpaces.Lift`: lifting bounds `LiftBound` (Bernstein's and Nikolskii's
  inequalities), dyadic near-best approximants `DyadicApprox`, and the telescoping construction.
  A lifting bound of exponent `β` gives `A^β_1 ↪ Y` (`exists_preimage_of_liftBound`).
* `ApproximationSpaces.Nikolskii`: the Nikolskii transfer theorem `A^s_q(X) ↪ B^{s-α}_q(Y)` for
  `0 ≤ α < s` (`exists_preimage_of_nikolskii`).

### Jackson inequalities and smoothness spaces

* `ApproximationSpaces.Jackson`: Jackson's inequality `JacksonBound`, which gives
  `ι(Y) ⊆ A^r_∞`, and smoothness spaces `SmoothnessSpace`, with `A^r_1 ⊆ ι(Y) ⊆ A^r_∞`.

### Real interpolation (`Interpolation/`)

* `ApproximationSpaces.Interpolation.KFunctional`: the K-functional `kFunctional` of a bounded
  linear map `ι : Y → X` and the spaces `(X, Y)_{θ,q}` of the discrete K-method (`interpNorm`,
  `MemInterp`).
* `ApproximationSpaces.Interpolation.Representation`: the representation theorem
  `A^s_q = (X, Y)_{s/r,q}` under Jackson's and Bernstein's inequalities of order `r`
  (`approxSpace_eq_interpSpace`).
* `ApproximationSpaces.Interpolation.KMethod`: the continuous K-method `kMethodNorm` and its
  equivalence with the discrete K-method on one-sided dyadic grids with an ambient-norm term
  (`memInterp_iff_memKMethod`), extending the classical two-sided comparison.
* `ApproximationSpaces.Interpolation.Couple`: couples `InterpCouple` of two extended quasi-norms
  on an abelian group, their K-functional and K-methods, and the couple `InterpCouple.ofMap ι`
  of a bounded linear map.
* `ApproximationSpaces.Interpolation.Property`: the interpolation property of the K-method,
  exact of exponent `θ` (`InterpCouple.kMethodNorm_map_le`), comparable couples and retracts.
* `ApproximationSpaces.Interpolation.Reiteration`: Holmstedt's formula in discrete form and the
  reiteration theorem `((X₀, X₁)_{θ₀,q₀}, (X₀, X₁)_{θ₁,q₁})_{η,q} = (X₀, X₁)_{(1-η)θ₀+ηθ₁,q}`
  (`InterpCouple.memKMethod_kCouple_iff`).
* `ApproximationSpaces.Interpolation.ApproxSpaces`: approximation spaces as interpolation
  spaces, `A^s_q = (X, A^r_∞)_{s/r,q}` for every scheme (`memApprox_iff_memKMethod_reprCouple`),
  their reiteration (`memKMethod_approxCouple_iff`) and the sandwich principle.
* `ApproximationSpaces.Interpolation.EFunctional`: the E-functional
  `E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}` of a couple (`InterpCouple.eFunctional`), its
  approximation spaces `E_{α,q}` (`InterpCouple.eMethodNorm`, `InterpCouple.MemEMethod`) and their
  dyadic norm `InterpCouple.eNormDyadic` (Bergh–Löfström, Section 7.1), the complexity couple of a
  sequence of sets and of increasing subgroups (`InterpCouple.ofMonotoneSubgroups`), and
  `E_{s,q} = A^s_q` for the complexity couple of a scheme
  (`memEMethod_complexityCouple_iff`).
* `ApproximationSpaces.Interpolation.EFunctionalModuli`: moduli of smoothness compatible with a
  couple whose first norm has a subadditive `ρ`-th power (`InterpCouple.ModulusData`), and the
  coincidence of `E_{s,q}` with the classical space for `0 < s < θ`
  (`InterpCouple.ModulusData.memEMethod_iff_modNorm_lt_top`), as for `L_p`, `0 < p < 1`.

### Decompositions (`Decompositions/`)

* `ApproximationSpaces.Decompositions.Projection`: schemes with uniformly bounded projections
  `ProjectionScheme` and the characterisation of `A^s_q` by dyadic blocks.
* `ApproximationSpaces.Decompositions.Blocks`: the characterisation of `A^s_q` by block
  decompositions `f = ∑ g_k` with `g_k ∈ A (2^k)` (`memApprox_iff_blockDecompNorm_lt_top`).
* `ApproximationSpaces.Decompositions.Synthesis`: linear schemes `IsLinear` and synthesis from
  blocks that are approximable at rate `σ` (`approxNormDyadic_le_of_hasSum_decay`).
* `ApproximationSpaces.Decompositions.Atomic`: atomic systems `AtomicSystem`, the sequence
  spaces `b^s_{p,q}` and the atomic characterisation of `A^s_q`
  (`AtomicSystem.memApprox_iff_exists_atomic`).

### Traces, retracts and moduli of smoothness

* `ApproximationSpaces.Trace`: maps controlled only on the approximants (`TraceBound`), their
  extension to `A^β_1`, the transfer `A^s_q(X) → B^{s-β}_q(Y)` and its surjectivity.
* `ApproximationSpaces.Retract`: approximation-preserving extensions `ApproxExtension` and the
  equivalence of intrinsic and restriction quasi-norms (`memApprox_iff_exists_restrict`).
* `ApproximationSpaces.Moduli`: moduli of smoothness compatible with a scheme (`ModulusData`),
  the coincidence of `A^s_q` with the classical space for `0 < s < θ`, and the interpolation of
  the classical spaces.
-/
