/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.WeakGradient
public import LeanPool.EllipticPDE.Regularity.Interior


/-!
# Bridge from `HasWeakDerivOn` to `HasWeakGradOn`

The `L²` weak derivatives produced by `interior_H2_estimate` are pointwise weak
gradients in the sense of the embedding layer, so the Morrey inequality consumes them
directly at `p = 2`, hence in dimension one.

Higher dimensions need an `Lᵖ` bootstrap first, since Morrey asks for `p > d`. Dimensions two and
three are covered in `EllipticPdes.Embedding.GagliardoNirenberg`, where the
Gagliardo-Nirenberg-Sobolev inequality raises the gradient from `L²` to `L⁶` at `d = 3` and, over
the finite measure of a ball, from `L^{4/3}` to `L⁴` at `d = 2`. The three resulting Hölder
estimates are `EllipticPdes.Embedding.interior_holder_estimate_one`,
`EllipticPdes.Embedding.interior_holder_estimate_two` and
`EllipticPdes.Embedding.interior_holder_estimate`.

Dimension four and above needs the step iterated, which uses a weak derivative per rung and so
asks for more than the `H²` estimate supplies. `EllipticPdes.Embedding.memLp_of_gradClosed` runs
that ladder on a family closed under differentiation.
-/

@[expose] public section

open MeasureTheory Set Metric

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- An `L²` weak gradient (componentwise `HasWeakDerivOn`) is a pointwise weak
gradient. This connects `interior_H2_estimate`'s output into `morrey_ball`. -/
theorem hasWeakGradOn_of_hasWeakDerivOn {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : Lp ℝ 2 (volume.restrict B)} {g : Fin d → Lp ℝ 2 (volume.restrict B)}
    (h : ∀ k, EllipticPdes.Regularity.HasWeakDerivOn B k u (g k)) :
    HasWeakGradOn B (fun x => (u x : ℝ)) (fun k x => (g k x : ℝ)) := by
  intro φ hφc hφcs hφB k
  exact h k φ hφc hφcs hφB

end EllipticPdes.Embedding
