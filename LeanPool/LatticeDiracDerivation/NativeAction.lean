/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/NativeAction.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.ExteriorArea
public import LeanPool.LatticeDiracDerivation.C19Geometry

/-! Frozen noncanonical DIRAC-002 action. -/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators

def sitePotential (chi0 : ℝ) (state : State Site) (site : Site) : ℝ :=
  let rhoPsi := density (state.psi site)
  let rhoChi := density (state.chi site)
  (rhoChi - chi0 ^ 2) ^ 2 / 4 + rhoChi * rhoPsi / 2 + rhoPsi ^ 2 / 4

def potential [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site) : ℝ :=
  (∑ site, sitePotential chi0 state site) +
    ∑ edge, exteriorAreaBond chi0 state (bond edge)

def lagrangian [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) : ℝ :=
  kinetic B velocity - potential chi0 state bond

def hamiltonian [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) : ℝ :=
  kinetic B velocity + potential chi0 state bond

def c19Potential [Fintype Site]
    (chi0 : ℝ) (state : State Site) (geometry : C19Lattice Site) : ℝ :=
  potential (Edge := C19Edge Site) chi0 state (c19Bond geometry)

def c19Lagrangian [Fintype Site]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (geometry : C19Lattice Site) : ℝ :=
  lagrangian (Edge := C19Edge Site) chi0 B state velocity (c19Bond geometry)

def c19Hamiltonian [Fintype Site]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (geometry : C19Lattice Site) : ℝ :=
  hamiltonian (Edge := C19Edge Site) chi0 B state velocity (c19Bond geometry)

theorem site_potential_nonnegative
    (chi0 : ℝ) (state : State Site) (site : Site) :
    0 ≤ sitePotential chi0 state site := by
  unfold sitePotential
  dsimp
  have hp := density_nonnegative (state.psi site)
  have hx := density_nonnegative (state.chi site)
  positivity

theorem potential_nonnegative [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (hchi : 0 < chi0) (hweight : ∀ edge, 0 ≤ (bond edge).weight) :
    0 ≤ potential chi0 state bond := by
  unfold potential
  apply add_nonneg
  · exact Finset.sum_nonneg (fun site _ =>
      site_potential_nonnegative chi0 state site)
  · exact Finset.sum_nonneg (fun edge _ =>
      exterior_area_bond_nonnegative chi0 state (bond edge)
        hchi (hweight edge))

theorem hamiltonian_nonnegative [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (hchi : 0 < chi0) (hB : 0 ≤ B)
    (hweight : ∀ edge, 0 ≤ (bond edge).weight) :
    0 ≤ hamiltonian chi0 B state velocity bond := by
  exact add_nonneg (kinetic_nonnegative B velocity hB)
    (potential_nonnegative chi0 state bond hchi hweight)

theorem c19_hamiltonian_nonnegative [Fintype Site]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (geometry : C19Lattice Site) (hchi : 0 < chi0) (hB : 0 ≤ B) :
    0 ≤ c19Hamiltonian chi0 B state velocity geometry := by
  exact hamiltonian_nonnegative chi0 B state velocity (c19Bond geometry)
    hchi hB (fun edge => le_of_lt (c19_bond_weight_positive geometry edge))

theorem total_capacity_coefficients_unique
    (a mu chi0 : ℝ) (hunit : 4 * a = 1)
    (hvacuum : 2 * mu = chi0 ^ 2) :
    a = 1/4 ∧ mu = chi0 ^ 2/2 := by
  constructor <;> linarith

theorem total_capacity_expansion (rhoChi rhoPsi chi0 : ℝ) :
    (rhoChi + rhoPsi) ^ 2 / 4 - chi0 ^ 2 * rhoChi / 2 + chi0 ^ 4 / 4 =
      (rhoChi - chi0 ^ 2) ^ 2 / 4 +
        rhoChi * rhoPsi / 2 + rhoPsi ^ 2 / 4 := by
  ring

end
end LeanDirac
