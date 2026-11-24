/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingFacts
public import LeanPool.GraphMinor.GM14.Cited

/-!
# Graph Minors XI, (6.3)

The paper states without proof (Section 3, page 75): "every region of $\Gamma'$ includes a unique
edge of
$\Gamma$", "unless $|V(\Gamma)| = 1$ and $E(\Gamma) = \emptyset$", and adds: "We omit the proofs of
these assertions, which
are elementary but rather tedious." The same sentence is used for the vertices on the closure of a
region (proof of (6.5), page 91).

This is `regionFacts_of_radial` for a drawing and `regionFacts_of_painting` for a painting. With
them,
`theorem_6_3` proves `GM14.GM11Theorem63Statement` with no hypothesis, by the paper's proof.
-/

@[expose] public section

namespace GraphMinor.GM11

open GraphMinor.Surface

universe u

/-- **(6.3)** of Graph Minors XI (page 89). -/
theorem theorem_6_3_proof : GM14.GM11Theorem63Statement.{u} := by
  intro S _ _ hS hc Γ Γ' θ T ins _ hE hT _ hrad hd
  have : T2Space S := hS.2.1
  cases Γ with
  | drawing Γ =>
    exact theorem_6_3_of_regionFacts hS hT hrad.2.1 hd (regionFacts_of_radial ⟨hrad.1,
      hrad.2.1⟩ hS hrad.2.2 hE)
  | painting Γ =>
    exact theorem_6_3_of_regionFacts hS hT hrad.2.1 hd (regionFacts_of_painting ⟨hrad.1,
      hrad.2.1⟩ hrad.2.2 hS hE)

end GraphMinor.GM11
