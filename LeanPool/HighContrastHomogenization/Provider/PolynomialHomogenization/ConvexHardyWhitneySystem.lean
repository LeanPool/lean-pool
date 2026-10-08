/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyChainAtCenter
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyRowScales
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexWhitneyGeometry

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyWhitneySystem

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Whitney rows with coherent convex Hardy chains

A ball-sandwiched convex domain admits maximal triadic Whitney rows together
with one coherent interior-ball chain for every selected cell.  The top row is
chosen at the inner-ball scale, all chains use the same sandwich center, and
distinct rows have distinct dyadic chain lengths.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix

noncomputable section

variable {d : ℕ}

/-- Maximal Whitney rows equipped with coherent chains to one fixed inner
ball. -/
structure ConvexHardyWhitneySystem (U : Set (Vec d)) (rho Rad : ℝ) where
  /-- Common center of the inner and outer balls bounding `U`. -/
  center : Vec d
  inner_ball : euclideanBallAt center rho ⊆ U
  outer_ball : U ⊆ euclideanBallAt center Rad
  /-- Whitney cutoff generation satisfying `3 ^ topScale ≤ rho < 3 ^ (topScale + 1)`. -/
  topScale : ℤ
  topScale_lower : (3 : ℝ) ^ topScale ≤ rho
  topScale_upper : rho < (3 : ℝ) ^ (topScale + 1)
  /-- Finite grid indices of the maximal Euclidean Whitney cells in each generation. -/
  rows : ℤ → Finset (Fin d → ℤ)
  rows_eq : ∀ a,
    ↑(rows a) = Transport.fillingIndex (1 : Mat d) topScale U a
  cell_subset : ∀ a, ∀ w ∈ rows a,
    standardCell d a w ⊆ U
  parent_escape : ∀ a, a < topScale → ∀ w ∈ rows a,
    ¬standardCell d (a + 1) (Transport.gridParent w) ⊆ U
  pairwise_disjoint : ∀ a b : ℤ, ∀ w ∈ rows a, ∀ v ∈ rows b,
    (a, w) ≠ (b, v) → Disjoint (standardCell d a w) (standardCell d b v)
  row_volume : ∀ a : ℤ, a < topScale →
    ∑ w ∈ rows a, volume (standardCell d a w) ≤
      ENNReal.ofReal
        (6 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ a / rho) * volume U
  ae_exhaustion :
    volume (U \ ⋃ a ∈ Set.Iic topScale, ⋃ w ∈ (rows a : Set (Fin d → ℤ)),
      standardCell d a w) = 0
  /-- Length shared by the Hardy ball chains in each Whitney generation. -/
  chainLength : {a : ℤ // a ≤ topScale} → ℕ
  chainLength_bounds : ∀ a : {a : ℤ // a ≤ topScale},
    (3 : ℝ) ^ (a : ℤ) ≤
        convexHardyBallChainRadius rho (chainLength a) 0 ∧
      convexHardyBallChainRadius rho (chainLength a) 0 <
        2 * (3 : ℝ) ^ (a : ℤ)
  chainLength_injective : Function.Injective chainLength
  /-- A Hardy ball chain from each selected cell center to the common inner ball. -/
  chain : ∀ a : {a : ℤ // a ≤ topScale}, ∀ w : ↑(rows a.1),
    ConvexHardyBallChain U (standardCellCenter a.1 w.1) rho Rad
      ((3 : ℝ) ^ a.1)
  chain_center : ∀ a w, (chain a w).center = center
  chain_length : ∀ a w, (chain a w).length = chainLength a

/-- Every ball-sandwiched bounded open convex domain has coherent maximal
Whitney rows and straight chains to a common inner ball. -/
theorem exists_convexHardyWhitneySystem (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {rho Rad : ℝ} (hsand : HasBallSandwich U rho Rad) :
    Nonempty (ConvexHardyWhitneySystem U rho Rad) := by
  classical
  obtain ⟨hrho, hRad, c, hinner, houter⟩ := hsand
  obtain ⟨n, hnlow, hnup⟩ :=
    exists_mem_Ico_zpow hrho (by norm_num : (1 : ℝ) < 3)
  obtain ⟨Z, hZ, hcell, hparent, hdisj, hrow, hcover⟩ :=
    exists_convex_whitney_rows hd hU
      ⟨hrho, hRad, c, hinner, houter⟩ n
  obtain ⟨N, hN, hNinj⟩ :=
    exists_injective_convexHardyRowChainLengths hrho hnlow
  have hchainExists : ∀ a : {a : ℤ // a ≤ n}, ∀ w : ↑(Z a.1),
      ∃ chain : ConvexHardyBallChain U (standardCellCenter a.1 w.1)
          rho Rad ((3 : ℝ) ^ a.1),
        chain.center = c ∧ chain.length = N a := by
    intro a w
    have hx : standardCellCenter a.1 w.1 ∈ U :=
      hcell a.1 w.1 w.property
        (Recurrence.standardCellCenter_mem_standardCell a.1 w.1)
    exact exists_convexHardyBallChain_at_center_of_length hd hU
      hrho hRad hinner houter hx (N a) (hN a).1 (hN a).2
  choose chain hchainCenter hchainLength using hchainExists
  exact ⟨{
    center := c
    inner_ball := hinner
    outer_ball := houter
    topScale := n
    topScale_lower := hnlow
    topScale_upper := hnup
    rows := Z
    rows_eq := hZ
    cell_subset := hcell
    parent_escape := hparent
    pairwise_disjoint := hdisj
    row_volume := hrow
    ae_exhaustion := hcover
    chainLength := N
    chainLength_bounds := hN
    chainLength_injective := hNinj
    chain := chain
    chain_center := hchainCenter
    chain_length := hchainLength }⟩

end

end HighContrast
end HCPolySupport
