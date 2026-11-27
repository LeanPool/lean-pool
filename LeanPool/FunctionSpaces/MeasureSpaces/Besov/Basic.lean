/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Scheme
public import LeanPool.FunctionSpaces.ApproximationSpaces.Space

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces as approximation spaces

Let `S` be a scheme of functions on `Ω` and `μ` a finite measure.  The **Besov space**
`B^s_{p,q}(Ω, S)` is the approximation space of `L_p(μ)` for the scheme `S`:

`B^s_{p,q} = A^s_q(L_p(μ), S)`,   `‖f‖_{B^s_{p,q}} = ‖(n^(s-1/q) E_{n-1}(f)_p)_n‖_{ℓ_q}`,

where `E_n(f)_p` is the error of best `L_p` approximation of `f` from `S n`, the
`ApproximationScheme.approxError` of the transported scheme `S.toLp μ p`.  On the torus with
`S n` the trigonometric polynomials of degree `< n` these are the classical periodic Besov
spaces; for other schemes (splines, wavelets, eigenfunctions) one obtains the Besov spaces
adapted to the scheme.  Whether they agree with a definition through moduli of smoothness is
a separate theorem for each scheme (Jackson and Bernstein inequalities).

The names in this file are abbreviations for the general notions of `ApproximationSpaces`, so
every result proved there applies to Besov spaces directly.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (S : FunctionScheme Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **Besov quasi-norm** `‖f‖_{B^s_{p,q}}`, Pietsch's quasi-norm of `A^s_q(L_p(μ), S)`. -/
noncomputable abbrev besovNorm (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : ℝ≥0∞ :=
  (S.toLp μ p).approxNorm s q f

/-- `f` belongs to the **Besov space** `B^s_{p,q}(Ω, S)`. -/
abbrev MemBesov (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : Prop := (S.toLp μ p).MemApprox s q f

/-- The **Besov space** `B^s_{p,q}(Ω, S)` as a real subspace of `L_p(μ)`, for `s ≥ 0`,
`1 ≤ q ≤ ∞`. -/
noncomputable abbrev besovSpace (s : ℝ) (q : ℝ≥0∞) (hs : 0 ≤ s) (hq : 1 ≤ q) :
    Submodule ℝ (Lp ℂ p μ) :=
  (S.toLp μ p).approxSpace s q hs hq

/-- The **uniform Besov space**: the approximation space of `S` in the sup norm, a space of
bounded continuous functions. -/
noncomputable abbrev besovSpaceSup (s : ℝ) (q : ℝ≥0∞) (hs : 0 ≤ s) (hq : 1 ≤ q) :
    Submodule ℝ (Ω →ᵇ ℂ) :=
  S.approxSpace s q hs hq

end FunctionScheme
