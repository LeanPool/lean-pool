/-
Copyright (c) 2026 Paul-Olivier Dehaye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Olivier Dehaye
-/
module

public import LeanPool.Giambelli.Basic
public import LeanPool.Giambelli.Schur

/-!
# Giambelli's identity for Schur polynomials

Source: url:https://github.com/DataDotFoundation/RMTlib/blob/ac695b1/RMTlib/Symmetric/Giambelli.lean
Authors: Paul-Olivier Dehaye
Status: verified
Main declarations: `Giambelli.diagramSchurPoly_eq_det_hook`, `Giambelli.schurPoly_eq_det_hook`,
  `Giambelli.giambelli_jt'`
Tags: symmetric-functions, schur-polynomials, determinants, young-diagrams
MSC: 05E05, 15A15
-/

@[expose] public section

/-!
## Mathematical overview

For a partition `λ` with Durfee square of side `d` and Frobenius coordinates
`λ = (α₀, …, α_{d−1} | β₀, …, β_{d−1})`, Giambelli's identity expresses the Schur polynomial as
the determinant of hook Schur polynomials, `s_λ = det (s_{(αᵢ | βⱼ)})_{i, j < d}`. The identity
is classical; see Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, §3,
Example 9.

`LeanPool.Giambelli.Basic` proves it for Jacobi–Trudi determinants of any pair of symbols `h, e`
with `H(X) E(−X) = 1`. `LeanPool.Giambelli.Schur` specializes it to Tau Ceti's Schur polynomials
through Tau Ceti's Jacobi–Trudi identity and `h`–`e` convolution.

## Main results

- `Giambelli.diagramSchurPoly_eq_det_hook`: Giambelli's identity for Young diagrams, in the
  alphabet `Fin N`.
- `Giambelli.schurPoly_eq_det_hook`: Giambelli's identity for partitions, in any finite alphabet.
- `Giambelli.giambelli_jt'`: Giambelli's identity for Jacobi–Trudi determinants of an `(h, e)`
  pair.

## Provenance

This is a port of `RMTlib/Symmetric/Giambelli.lean` from DataDotFoundation/RMTlib (commit
`ac695b1`). The Lean proofs were produced with AI (Claude). The formalization was motivated by
P.-O. Dehaye, *Combinatorics of lower order terms in the moment conjectures for the Riemann zeta
function*, arXiv:1201.4478, §7.1.4, which uses Giambelli's identity in the Frobenius–Schur form of
Olshanski–Regev–Vershik. This project proves the classical Schur form.
-/
