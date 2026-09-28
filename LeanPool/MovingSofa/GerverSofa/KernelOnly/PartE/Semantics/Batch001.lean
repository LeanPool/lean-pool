/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Foundation.Batch004
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.DeepMindABPhiThetaBridge`.
* `KernelOnly.PartE.TwoAngleReduction`.
* `KernelOnly.PartE.ScaledResidualInterval`.
* `KernelOnly.PartE.FiniteCoverReplay`.
* `KernelOnly.PartE.LocalTwoAngleKrawczykClosure`.
* `KernelOnly.PartE.AdaptiveGlobalCoverClosure`.
* `KernelOnly.PartE.E24AlignedRegionFoundation`.
* `KernelOnly.PartE.E24AlignedLogic`.
* `KernelOnly.PartE.E24KC2ProofHelpers`.
* `KernelOnly.PartE.E24PhiBelowKernelHL`.
-/

@[expose] public section

noncomputable section


section

/-!
# Part E01: bridge to DeepMind's Gerver-constant specification

This module mirrors the four equations and the physical domain used by
`GerversSofa.ABφθSpec` in `google-deepmind/formal-conjectures`.  It proves that
the four displayed equations are exactly the already certified reduced Gerver
system, proves that the certified rational box lies in the physical domain,
and reduces the tuple-shaped global uniqueness statement to one explicit
global enclosure target.

The enclosure target is a proposition passed as an ordinary theorem argument.
E01 does not claim that the global exclusion step has already been proved.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

/-- Reduced parameters assembled in the order `(A, B, phi, theta)`. -/
def reducedParams (A B phi theta : ℝ) : Reduced.Params :=
  { a := A, b := B, phi := phi, theta := theta }

/-- The physical domain appearing in DeepMind's `ABφθSpec`. -/
def PhysicalDomain (p : Reduced.Params) : Prop :=
  0 ≤ p.phi ∧ p.phi ≤ p.theta ∧ p.theta ≤ Real.pi / 4 ∧
    0 ≤ p.a ∧ 0 ≤ p.b

/-- The four displayed equations in DeepMind's `ABφθSpec`. -/
def DeepMindEquations (A B phi theta : ℝ) : Prop :=
  A * (Real.cos theta - Real.cos phi) - 2 * B * Real.sin phi
      + (theta - phi - 1) * Real.cos theta - Real.sin theta
      + Real.cos phi + Real.sin phi = 0 ∧
  A * (3 * Real.sin theta + Real.sin phi) - 2 * B * Real.cos phi
      + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
      - Real.sin phi + Real.cos phi = 0 ∧
  A * Real.cos phi
      - (Real.sin phi + 1 / 2 - Real.cos phi / 2 + B * Real.sin phi) = 0 ∧
  (A + Real.pi / 2 - phi - theta)
      - (B - (theta - phi) * (1 + A) / 2 - (theta - phi) ^ 2 / 4) = 0

/-- A local mirror of DeepMind's complete four-constant specification. -/
def DeepMindABPhiThetaSpec (A B phi theta : ℝ) : Prop :=
  PhysicalDomain (reducedParams A B phi theta) ∧
    DeepMindEquations A B phi theta

/-- Explicit equivalence between DeepMind's four equations and the certified
reduced Gerver system. -/
theorem deepMindEquations_iff_reducedEquations (A B phi theta : ℝ) :
    DeepMindEquations A B phi theta ↔
      Reduced.Equations (reducedParams A B phi theta) := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    change Reduced.system (reducedParams A B phi theta) = 0
    funext i
    fin_cases i
    · change
        A * (Real.cos theta - Real.cos phi) - 2 * B * Real.sin phi
            + (theta - phi - 1) * Real.cos theta - Real.sin theta
            + Real.cos phi + Real.sin phi = 0
      exact h0
    · change
        A * (3 * Real.sin theta + Real.sin phi) - 2 * B * Real.cos phi
            + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
            - Real.sin phi + Real.cos phi = 0
      exact h1
    · change
        A * Real.cos phi - Real.sin phi - 1 / 2
            + 1 / 2 * Real.cos phi - B * Real.sin phi = 0
      ring_nf at h2 ⊢
      exact h2
    · change
        A + Real.pi / 2 - phi - theta - B
            + 1 / 2 * (theta - phi) * (1 + A)
            + 1 / 4 * (theta - phi) * (theta - phi) = 0
      ring_nf at h3 ⊢
      exact h3
  · intro h
    change Reduced.system (reducedParams A B phi theta) = 0 at h
    have h0 := congrFun h (0 : Fin 4)
    have h1 := congrFun h (1 : Fin 4)
    have h2 := congrFun h (2 : Fin 4)
    have h3 := congrFun h (3 : Fin 4)
    change
      A * (Real.cos theta - Real.cos phi) - 2 * B * Real.sin phi
          + (theta - phi - 1) * Real.cos theta - Real.sin theta
          + Real.cos phi + Real.sin phi = 0 at h0
    change
      A * (3 * Real.sin theta + Real.sin phi) - 2 * B * Real.cos phi
          + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
          - Real.sin phi + Real.cos phi = 0 at h1
    change
      A * Real.cos phi - Real.sin phi - 1 / 2
          + 1 / 2 * Real.cos phi - B * Real.sin phi = 0 at h2
    change
      A + Real.pi / 2 - phi - theta - B
          + 1 / 2 * (theta - phi) * (1 + A)
          + 1 / 4 * (theta - phi) * (theta - phi) = 0 at h3
    refine ⟨h0, h1, ?_, ?_⟩
    · ring_nf at h2 ⊢
      exact h2
    · ring_nf at h3 ⊢
      exact h3

/-- Every point of the certified reduced box satisfies DeepMind's broad
physical-domain inequalities. -/
theorem physicalDomain_of_mem_reducedBox {p : Reduced.Params}
    (hp : p ∈ Reduced.box) : PhysicalDomain p := by
  dsimp [Reduced.box, qR] at hp
  rcases hp with
    ⟨haLo, _haHi, hbLo, _hbHi, hphiLo, hphiHi, hthetaLo, hthetaHi⟩
  have hphiNonneg : 0 ≤ p.phi := by
    have hconst :
        (0 : ℝ) ≤ (122429264969 : ℝ) / 3125000000000 := by
      norm_num
    exact hconst.trans hphiLo
  have hphiTheta : p.phi ≤ p.theta := by
    have hgap :
        (3917736479009 : ℝ) / 100000000000000 ≤
          (2129067216821 : ℝ) / 3125000000000 := by
      norm_num
    exact hphiHi.trans (hgap.trans hthetaLo)
  have hthetaPi : p.theta ≤ Real.pi / 4 := by
    have hrat :
        (68130150938273 : ℝ) / 100000000000000 < (3 : ℝ) / 4 := by
      norm_num
    have hthree : (3 : ℝ) / 4 < Real.pi / 4 := by
      nlinarith [Real.pi_gt_three]
    exact hthetaHi.trans (le_of_lt (hrat.trans hthree))
  have haNonneg : 0 ≤ p.a := by
    have hconst :
        (0 : ℝ) ≤ (1888531216873 : ℝ) / 20000000000000 := by
      norm_num
    exact hconst.trans haLo
  have hbNonneg : 0 ≤ p.b := by
    have hconst :
        (0 : ℝ) ≤ (69960186366677 : ℝ) / 50000000000000 := by
      norm_num
    exact hconst.trans hbLo
  exact ⟨hphiNonneg, hphiTheta, hthetaPi, haNonneg, hbNonneg⟩

/-- The mirrored DeepMind specification is precisely physical-domain
membership plus the already named reduced equations. -/
theorem deepMindSpec_iff_physicalDomain_and_reducedEquations
    (A B phi theta : ℝ) :
    DeepMindABPhiThetaSpec A B phi theta ↔
      PhysicalDomain (reducedParams A B phi theta) ∧
        Reduced.Equations (reducedParams A B phi theta) := by
  unfold DeepMindABPhiThetaSpec
  rw [deepMindEquations_iff_reducedEquations]

/-- A certified-box solution of the reduced system is automatically a
solution of the mirrored DeepMind specification. -/
theorem deepMindSpec_of_mem_reducedBox_and_equations {p : Reduced.Params}
    (hp : p ∈ Reduced.box) (heq : Reduced.Equations p) :
    DeepMindABPhiThetaSpec p.a p.b p.phi p.theta := by
  apply
    (deepMindSpec_iff_physicalDomain_and_reducedEquations
      p.a p.b p.phi p.theta).2
  simpa [reducedParams] using
    And.intro (physicalDomain_of_mem_reducedBox hp) heq

/-- The sole new mathematical target left after E01: every physical solution
of the reduced equations lies in the already certified rational box. -/
def GlobalEnclosureTarget : Prop :=
  ∀ p : Reduced.Params,
    PhysicalDomain p → Reduced.Equations p → p ∈ Reduced.box

/-- Coordinate equivalence between DeepMind's nested tuple and the named
reduced-parameter record. -/
def tupleEquiv : (ℝ × ℝ × ℝ × ℝ) ≃ Reduced.Params where
  toFun x := reducedParams x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun p := (p.a, p.b, p.phi, p.theta)
  left_inv x := by
    rcases x with ⟨A, B, phi, theta⟩
    rfl
  right_inv p := by
    cases p
    rfl

/-- Once the explicit global enclosure theorem is supplied, the existing
kernel-checked local certificate yields the exact tuple-shaped uniqueness
statement required by DeepMind. -/
theorem deepMindABPhiTheta_existsUnique_of_globalEnclosure
    (hglobal : GlobalEnclosureTarget) :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 := by
  let cert := PartALeanCert.reducedCertifiedUniqueSolution
  refine ⟨tupleEquiv.symm cert.solution, ?_, ?_⟩
  · change
      DeepMindABPhiThetaSpec
        cert.solution.a cert.solution.b cert.solution.phi cert.solution.theta
    exact
      deepMindSpec_of_mem_reducedBox_and_equations
        cert.solution_mem cert.satisfies
  · intro y hy
    apply tupleEquiv.injective
    rw [tupleEquiv.apply_symm_apply]
    apply cert.unique (tupleEquiv y)
    · apply hglobal (tupleEquiv y)
      · exact
          ((deepMindSpec_iff_physicalDomain_and_reducedEquations
            y.1 y.2.1 y.2.2.1 y.2.2.2).1 hy).1
      · exact
          ((deepMindSpec_iff_physicalDomain_and_reducedEquations
            y.1 y.2.1 y.2.2.1 y.2.2.2).1 hy).2
    · exact
        ((deepMindSpec_iff_physicalDomain_and_reducedEquations
          y.1 y.2.1 y.2.2.1 y.2.2.2).1 hy).2

end PartE
end GerverSofa

end

end

end

section

/-!
# Part E02: exact reduction of the DeepMind system to two angles

E01 identified the sole missing mathematical input as a global enclosure of
all physical solutions of the four-variable reduced system.  E02 eliminates
the two linear variables `A` and `B` exactly.

The third and fourth Gerver equations first give `B` as an affine expression
in `A`, and then give `A` as a quotient depending only on `(phi, theta)`.  The
denominator is proved nonzero for every physical solution; this is a theorem,
not an additional assumption.  Consequently existence of a physical
four-variable solution is equivalent to a two-angle specification.

The remaining enclosure target quantifies only over
`0 <= phi <= theta <= pi/4`.  It is still an ordinary theorem argument: E02
does not declare the interval branch-and-bound conclusion as an axiom.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

/-- Difference of the two switching angles. -/
def angleDelta (phi theta : ℝ) : ℝ := theta - phi

/-- Constant part of the fourth equation after solving it for `B`. -/
def bBase (phi theta : ℝ) : ℝ :=
  Real.pi / 2 - phi - theta + angleDelta phi theta / 2 +
    angleDelta phi theta ^ 2 / 4

/-- The value of `B` forced by the fourth equation once `A` is fixed. -/
def bFromA (A phi theta : ℝ) : ℝ :=
  A * (1 + angleDelta phi theta / 2) + bBase phi theta

/-- Denominator obtained from the third equation after eliminating `B`. -/
def angleDenominator (phi theta : ℝ) : ℝ :=
  Real.cos phi - (1 + angleDelta phi theta / 2) * Real.sin phi

/-- Numerator obtained from the third equation after eliminating `B`. -/
def angleNumerator (phi theta : ℝ) : ℝ :=
  Real.sin phi + 1 / 2 - Real.cos phi / 2 +
    bBase phi theta * Real.sin phi

/-- Reconstructed value of `A`, depending only on the two angles. -/
def reconstructedA (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta / angleDenominator phi theta

/-- Reconstructed value of `B`, depending only on the two angles. -/
def reconstructedB (phi theta : ℝ) : ℝ :=
  bFromA (reconstructedA phi theta) phi theta

/-- The triangular physical domain for the two switching angles. -/
def PhysicalAngleDomain (phi theta : ℝ) : Prop :=
  0 ≤ phi ∧ phi ≤ theta ∧ theta ≤ Real.pi / 4

/-- The last two displayed equations of the DeepMind system. -/
def ThirdFourthEquations (A B phi theta : ℝ) : Prop :=
  A * Real.cos phi
      - (Real.sin phi + 1 / 2 - Real.cos phi / 2 + B * Real.sin phi) = 0 ∧
  (A + Real.pi / 2 - phi - theta)
      - (B - (theta - phi) * (1 + A) / 2 - (theta - phi) ^ 2 / 4) = 0

/-- The fourth equation is exactly the affine reconstruction formula for `B`. -/
theorem fourthEquation_iff_b_eq_bFromA (A B phi theta : ℝ) :
    (A + Real.pi / 2 - phi - theta)
          - (B - (theta - phi) * (1 + A) / 2 -
            (theta - phi) ^ 2 / 4) = 0 ↔
      B = bFromA A phi theta := by
  constructor <;> intro h <;>
    dsimp [bFromA, bBase, angleDelta] at h ⊢ <;>
    ring_nf at h ⊢ <;>
    linarith

/-- After the fourth equation has reconstructed `B`, the third equation is
exactly `A * denominator = numerator`. -/
theorem thirdEquation_iff_mul_denominator_eq_numerator
    (A B phi theta : ℝ) (hB : B = bFromA A phi theta) :
    A * Real.cos phi
          - (Real.sin phi + 1 / 2 - Real.cos phi / 2 +
            B * Real.sin phi) = 0 ↔
      A * angleDenominator phi theta = angleNumerator phi theta := by
  subst B
  constructor <;> intro h <;>
    dsimp [bFromA, bBase, angleDelta, angleDenominator,
      angleNumerator] at h ⊢ <;>
    ring_nf at h ⊢ <;>
    linarith

/-- Exact simultaneous elimination statement for equations three and four. -/
theorem thirdFourthEquations_iff_eliminated (A B phi theta : ℝ) :
    ThirdFourthEquations A B phi theta ↔
      B = bFromA A phi theta ∧
        A * angleDenominator phi theta = angleNumerator phi theta := by
  constructor
  · rintro ⟨h3, h4⟩
    have hB := (fourthEquation_iff_b_eq_bFromA A B phi theta).1 h4
    exact ⟨hB,
      (thirdEquation_iff_mul_denominator_eq_numerator
        A B phi theta hB).1 h3⟩
  · rintro ⟨hB, hA⟩
    exact ⟨
      (thirdEquation_iff_mul_denominator_eq_numerator
        A B phi theta hB).2 hA,
      (fourthEquation_iff_b_eq_bFromA A B phi theta).2 hB⟩

/-- The physical four-variable domain projects to the triangular angle domain. -/
theorem physicalAngleDomain_of_physicalDomain {A B phi theta : ℝ}
    (h : PhysicalDomain (reducedParams A B phi theta)) :
    PhysicalAngleDomain phi theta := by
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The constant part of the reconstructed `B` is nonnegative throughout the
physical angle triangle. -/
theorem bBase_nonneg_of_physicalAngleDomain {phi theta : ℝ}
    (h : PhysicalAngleDomain phi theta) : 0 ≤ bBase phi theta := by
  rcases h with ⟨hphi0, hphiTheta, htheta⟩
  have hdelta : 0 ≤ theta - phi := sub_nonneg.mpr hphiTheta
  have hsum : phi + theta ≤ Real.pi / 2 := by
    nlinarith
  have hsquare : 0 ≤ (theta - phi) ^ 2 := sq_nonneg (theta - phi)
  dsimp [bBase, angleDelta]
  nlinarith

/-- The sine of the first switching angle is nonnegative in the physical
triangle. -/
theorem sin_phi_nonneg_of_physicalAngleDomain {phi theta : ℝ}
    (h : PhysicalAngleDomain phi theta) : 0 ≤ Real.sin phi := by
  rcases h with ⟨hphi0, hphiTheta, htheta⟩
  apply Real.sin_nonneg_of_nonneg_of_le_pi hphi0
  nlinarith [Real.pi_gt_three]

/-- The cosine of the first switching angle is strictly positive in the
physical triangle. -/
theorem cos_phi_pos_of_physicalAngleDomain {phi theta : ℝ}
    (h : PhysicalAngleDomain phi theta) : 0 < Real.cos phi := by
  rcases h with ⟨hphi0, hphiTheta, htheta⟩
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

/-- No physical solution of all four equations can hit the apparent zero
denominator of the two-angle reconstruction. -/
theorem angleDenominator_ne_zero_of_physical_and_equations
    {A B phi theta : ℝ}
    (hdom : PhysicalDomain (reducedParams A B phi theta))
    (heq : DeepMindEquations A B phi theta) :
    angleDenominator phi theta ≠ 0 := by
  have hang : PhysicalAngleDomain phi theta :=
    physicalAngleDomain_of_physicalDomain hdom
  have helim :
      B = bFromA A phi theta ∧
        A * angleDenominator phi theta = angleNumerator phi theta :=
    (thirdFourthEquations_iff_eliminated A B phi theta).1
      ⟨heq.2.2.1, heq.2.2.2⟩
  intro hden
  have hnumZero : angleNumerator phi theta = 0 := by
    rw [← helim.2, hden, mul_zero]
  have hsinNonneg : 0 ≤ Real.sin phi :=
    sin_phi_nonneg_of_physicalAngleDomain hang
  have hcosPos : 0 < Real.cos phi :=
    cos_phi_pos_of_physicalAngleDomain hang
  have hsinNe : Real.sin phi ≠ 0 := by
    intro hsin
    have hcosZero : Real.cos phi = 0 := by
      dsimp [angleDenominator, angleDelta] at hden
      rw [hsin, mul_zero, sub_zero] at hden
      exact hden
    exact (ne_of_gt hcosPos) hcosZero
  have hsinPos : 0 < Real.sin phi :=
    lt_of_le_of_ne hsinNonneg hsinNe.symm
  have hbaseNonneg : 0 ≤ bBase phi theta :=
    bBase_nonneg_of_physicalAngleDomain hang
  have hcosGap : 0 ≤ 1 / 2 - Real.cos phi / 2 := by
    nlinarith [Real.cos_le_one phi]
  have hbaseSin : 0 ≤ bBase phi theta * Real.sin phi :=
    mul_nonneg hbaseNonneg hsinNonneg
  have hnumPos : 0 < angleNumerator phi theta := by
    dsimp [angleNumerator]
    nlinarith
  exact (ne_of_gt hnumPos) hnumZero

/-- Every physical four-variable solution has the reconstructed value of `A`. -/
theorem a_eq_reconstructed_of_physical_and_equations
    {A B phi theta : ℝ}
    (hdom : PhysicalDomain (reducedParams A B phi theta))
    (heq : DeepMindEquations A B phi theta) :
    A = reconstructedA phi theta := by
  have hden :=
    angleDenominator_ne_zero_of_physical_and_equations hdom heq
  have helim :=
    (thirdFourthEquations_iff_eliminated A B phi theta).1
      ⟨heq.2.2.1, heq.2.2.2⟩
  exact (eq_div_iff hden).2 helim.2

/-- Every physical four-variable solution has the reconstructed value of `B`. -/
theorem b_eq_reconstructed_of_physical_and_equations
    {A B phi theta : ℝ}
    (hdom : PhysicalDomain (reducedParams A B phi theta))
    (heq : DeepMindEquations A B phi theta) :
    B = reconstructedB phi theta := by
  have hA := a_eq_reconstructed_of_physical_and_equations hdom heq
  have hB :=
    ((thirdFourthEquations_iff_eliminated A B phi theta).1
      ⟨heq.2.2.1, heq.2.2.2⟩).1
  calc
    B = bFromA A phi theta := hB
    _ = bFromA (reconstructedA phi theta) phi theta := by rw [hA]
    _ = reconstructedB phi theta := rfl

/-- The first two equations after exact reconstruction of `A` and `B`. -/
def TwoAngleEquations (phi theta : ℝ) : Prop :=
  let A := reconstructedA phi theta
  let B := reconstructedB phi theta
  A * (Real.cos theta - Real.cos phi) - 2 * B * Real.sin phi
      + (theta - phi - 1) * Real.cos theta - Real.sin theta
      + Real.cos phi + Real.sin phi = 0 ∧
  A * (3 * Real.sin theta + Real.sin phi) - 2 * B * Real.cos phi
      + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
      - Real.sin phi + Real.cos phi = 0

/-- Complete two-dimensional specification equivalent to existence of a
physical solution with the given two angles. -/
def TwoAngleSpec (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧
    angleDenominator phi theta ≠ 0 ∧
    0 ≤ reconstructedA phi theta ∧
    0 ≤ reconstructedB phi theta ∧
    TwoAngleEquations phi theta

/-- The reconstructed parameters assembled as a reduced-system record. -/
def reconstructedParams (phi theta : ℝ) : Reduced.Params :=
  reducedParams (reconstructedA phi theta) (reconstructedB phi theta) phi theta

/-- Two-angle data reconstruct a physical solution of all four displayed
DeepMind equations. -/
theorem deepMindSpec_of_twoAngleSpec {phi theta : ℝ}
    (h : TwoAngleSpec phi theta) :
    DeepMindABPhiThetaSpec
      (reconstructedA phi theta) (reconstructedB phi theta) phi theta := by
  rcases h with ⟨hang, hden, hA0, hB0, h12⟩
  have h34 : ThirdFourthEquations
      (reconstructedA phi theta) (reconstructedB phi theta) phi theta := by
    apply (thirdFourthEquations_iff_eliminated
      (reconstructedA phi theta) (reconstructedB phi theta) phi theta).2
    constructor
    · rfl
    · simp [reconstructedA, hden]
  refine ⟨?_, ?_⟩
  · exact ⟨hang.1, hang.2.1, hang.2.2, hA0, hB0⟩
  · rcases h12 with ⟨h1, h2⟩
    exact ⟨h1, h2, h34.1, h34.2⟩

/-- Exact dimension reduction: for fixed angles, a physical four-variable
solution exists if and only if the reconstructed two-angle specification
holds. -/
theorem exists_deepMindSpec_iff_twoAngleSpec (phi theta : ℝ) :
    (∃ A B : ℝ, DeepMindABPhiThetaSpec A B phi theta) ↔
      TwoAngleSpec phi theta := by
  constructor
  · rintro ⟨A, B, hspec⟩
    have hden := angleDenominator_ne_zero_of_physical_and_equations
      hspec.1 hspec.2
    have hA := a_eq_reconstructed_of_physical_and_equations hspec.1 hspec.2
    have hB := b_eq_reconstructed_of_physical_and_equations hspec.1 hspec.2
    refine ⟨physicalAngleDomain_of_physicalDomain hspec.1, hden, ?_, ?_, ?_⟩
    · have hA0 : 0 ≤ A := by
        simpa only [reducedParams] using hspec.1.2.2.2.1
      rw [hA] at hA0
      exact hA0
    · have hB0 : 0 ≤ B := by
        simpa only [reducedParams] using hspec.1.2.2.2.2
      rw [hB] at hB0
      exact hB0
    · rcases hspec.2 with ⟨h1, h2, _h3, _h4⟩
      simpa [TwoAngleEquations, hA, hB] using And.intro h1 h2
  · intro h
    exact ⟨reconstructedA phi theta, reconstructedB phi theta,
      deepMindSpec_of_twoAngleSpec h⟩

/-- The sole mathematical target left after E02.  Unlike E01's four-variable
target, this quantifies only over the compact triangle of the two angles. -/
def TwoAngleEnclosureTarget : Prop :=
  ∀ phi theta : ℝ,
    TwoAngleSpec phi theta → reconstructedParams phi theta ∈ Reduced.box

/-- A proof of the two-angle enclosure target yields E01's full global
enclosure target. -/
theorem globalEnclosureTarget_of_twoAngleEnclosure
    (hangle : TwoAngleEnclosureTarget) : GlobalEnclosureTarget := by
  intro p hdom heq
  have hdeep : DeepMindEquations p.a p.b p.phi p.theta :=
    (deepMindEquations_iff_reducedEquations
      p.a p.b p.phi p.theta).2 (by simpa [reducedParams] using heq)
  have hspec : DeepMindABPhiThetaSpec p.a p.b p.phi p.theta :=
    ⟨by simpa [reducedParams] using hdom, hdeep⟩
  have htwo : TwoAngleSpec p.phi p.theta :=
    (exists_deepMindSpec_iff_twoAngleSpec p.phi p.theta).1
      ⟨p.a, p.b, hspec⟩
  have hmem := hangle p.phi p.theta htwo
  have hA := a_eq_reconstructed_of_physical_and_equations hspec.1 hspec.2
  have hB := b_eq_reconstructed_of_physical_and_equations hspec.1 hspec.2
  change
    reducedParams
      (reconstructedA p.phi p.theta) (reconstructedB p.phi p.theta)
      p.phi p.theta ∈ Reduced.box at hmem
  rw [← hA, ← hB] at hmem
  simpa [reconstructedParams, reducedParams] using hmem

/-- Terminal E02 bridge: the exact DeepMind-shaped uniqueness theorem now
requires only the compact two-angle enclosure theorem. -/
theorem deepMindABPhiTheta_existsUnique_of_twoAngleEnclosure
    (hangle : TwoAngleEnclosureTarget) :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 :=
  deepMindABPhiTheta_existsUnique_of_globalEnclosure
    (globalEnclosureTarget_of_twoAngleEnclosure hangle)

end PartE
end GerverSofa

end

end

end

section

/-!
# Part E03: division-free two-angle residuals and interval rejection kernel

E02 reduced the four-variable DeepMind system to two angles, but its
reconstructed values contain a quotient.  Direct interval evaluation of that
quotient is unnecessarily singular near the corner where its denominator can
vanish.

This module clears the denominator exactly.  It proves that, whenever the E02
denominator is nonzero, the two original reconstructed equations are
equivalent to two smooth residuals containing only addition, multiplication,
`sin`, `cos`, and the named constant `pi`.

The same residuals are encoded as LeanCert expressions.  The final theorem is
a reusable, executable cell-rejection kernel: if certified interval evaluation
of either residual excludes zero on a rational rectangle, no common zero can
lie in that rectangle.  E03 intentionally does not postulate a global cover;
the finite branch-and-bound cover is the next data layer.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core
open LeanCert.Engine
open PartALeanCert

/-- First reconstructed E02 equation, written as a residual. -/
def firstReconstructedResidual (phi theta : ℝ) : ℝ :=
  reconstructedA phi theta * (Real.cos theta - Real.cos phi)
    - 2 * reconstructedB phi theta * Real.sin phi
    + (theta - phi - 1) * Real.cos theta - Real.sin theta
    + Real.cos phi + Real.sin phi

/-- Second reconstructed E02 equation, written as a residual. -/
def secondReconstructedResidual (phi theta : ℝ) : ℝ :=
  reconstructedA phi theta * (3 * Real.sin theta + Real.sin phi)
    - 2 * reconstructedB phi theta * Real.cos phi
    + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
    - Real.sin phi + Real.cos phi

/-- Numerator of `denominator * reconstructedB`, with no division. -/
def scaledB (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta * (1 + angleDelta phi theta / 2)
    + bBase phi theta * angleDenominator phi theta

/-- Division-free first residual. -/
def scaledResidualOne (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta * (Real.cos theta - Real.cos phi)
    - 2 * scaledB phi theta * Real.sin phi
    + (angleDelta phi theta - 1) * Real.cos theta
        * angleDenominator phi theta
    - Real.sin theta * angleDenominator phi theta
    + Real.cos phi * angleDenominator phi theta
    + Real.sin phi * angleDenominator phi theta

/-- Division-free second residual. -/
def scaledResidualTwo (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta * (3 * Real.sin theta + Real.sin phi)
    - 2 * scaledB phi theta * Real.cos phi
    + 3 * (angleDelta phi theta - 1) * Real.sin theta
        * angleDenominator phi theta
    + 3 * Real.cos theta * angleDenominator phi theta
    - Real.sin phi * angleDenominator phi theta
    + Real.cos phi * angleDenominator phi theta

/-- The cleared numerator is exactly `denominator * reconstructedB`. -/
theorem denominator_mul_reconstructedB_eq_scaledB
    (phi theta : ℝ) (hden : angleDenominator phi theta ≠ 0) :
    angleDenominator phi theta * reconstructedB phi theta =
      scaledB phi theta := by
  dsimp [reconstructedB, bFromA, reconstructedA, scaledB]
  field_simp [hden]


/-- The first smooth residual is the original residual multiplied by the
E02 denominator. -/
theorem scaledResidualOne_eq_denominator_mul
    (phi theta : ℝ) (hden : angleDenominator phi theta ≠ 0) :
    scaledResidualOne phi theta =
      angleDenominator phi theta * firstReconstructedResidual phi theta := by
  have hA : angleDenominator phi theta * reconstructedA phi theta =
      angleNumerator phi theta := by
    dsimp [reconstructedA]
    field_simp [hden]
  have hB := denominator_mul_reconstructedB_eq_scaledB phi theta hden
  unfold scaledResidualOne firstReconstructedResidual
  rw [← hA, ← hB]
  dsimp [angleDelta]
  ring

/-- The second smooth residual is the original residual multiplied by the
E02 denominator. -/
theorem scaledResidualTwo_eq_denominator_mul
    (phi theta : ℝ) (hden : angleDenominator phi theta ≠ 0) :
    scaledResidualTwo phi theta =
      angleDenominator phi theta * secondReconstructedResidual phi theta := by
  have hA : angleDenominator phi theta * reconstructedA phi theta =
      angleNumerator phi theta := by
    dsimp [reconstructedA]
    field_simp [hden]
  have hB := denominator_mul_reconstructedB_eq_scaledB phi theta hden
  unfold scaledResidualTwo secondReconstructedResidual
  rw [← hA, ← hB]
  dsimp [angleDelta]
  ring

/-- E02's two equations are exactly the vanishing of the two ordinary
reconstructed residuals. -/
theorem twoAngleEquations_iff_reconstructedResiduals_zero
    (phi theta : ℝ) :
    TwoAngleEquations phi theta ↔
      firstReconstructedResidual phi theta = 0 ∧
      secondReconstructedResidual phi theta = 0 := by
  rfl

/-- Exact denominator-clearing equivalence used by the interval layer. -/
theorem twoAngleEquations_iff_scaledResiduals_zero
    (phi theta : ℝ) (hden : angleDenominator phi theta ≠ 0) :
    TwoAngleEquations phi theta ↔
      scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0 := by
  rw [twoAngleEquations_iff_reconstructedResiduals_zero]
  rw [scaledResidualOne_eq_denominator_mul phi theta hden]
  rw [scaledResidualTwo_eq_denominator_mul phi theta hden]
  constructor
  · rintro ⟨h1, h2⟩
    simp [h1, h2]
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_eq_zero.mp h1).resolve_left hden,
      (mul_eq_zero.mp h2).resolve_left hden⟩

/-- The complete E02 specification with only smooth equations in its final
conjunct. -/
def ScaledTwoAngleSpec (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧
    angleDenominator phi theta ≠ 0 ∧
    0 ≤ reconstructedA phi theta ∧
    0 ≤ reconstructedB phi theta ∧
    scaledResidualOne phi theta = 0 ∧
    scaledResidualTwo phi theta = 0

/-- No mathematical information is lost by clearing the denominator. -/
theorem twoAngleSpec_iff_scaledTwoAngleSpec (phi theta : ℝ) :
    TwoAngleSpec phi theta ↔ ScaledTwoAngleSpec phi theta := by
  constructor
  · rintro ⟨hdom, hden, hA, hB, heq⟩
    exact ⟨hdom, hden, hA, hB,
      (twoAngleEquations_iff_scaledResiduals_zero phi theta hden).1 heq⟩
  · rintro ⟨hdom, hden, hA, hB, heq⟩
    exact ⟨hdom, hden, hA, hB,
      (twoAngleEquations_iff_scaledResiduals_zero phi theta hden).2 heq⟩

/-- E02's remaining enclosure target, now stated over division-free
equations. -/
def ScaledResidualEnclosureTarget : Prop :=
  ∀ phi theta : ℝ,
    ScaledTwoAngleSpec phi theta → reconstructedParams phi theta ∈ Reduced.box

/-- The smooth-residual enclosure target is exactly the E02 target. -/
theorem scaledResidualEnclosureTarget_iff_twoAngleEnclosureTarget :
    ScaledResidualEnclosureTarget ↔ TwoAngleEnclosureTarget := by
  constructor
  · intro h phi theta hspec
    exact h phi theta ((twoAngleSpec_iff_scaledTwoAngleSpec phi theta).1 hspec)
  · intro h phi theta hspec
    exact h phi theta ((twoAngleSpec_iff_scaledTwoAngleSpec phi theta).2 hspec)

/-! ## LeanCert expression model -/

/-- LeanCert AST for the two division-free residuals.  Variable 0 is `phi`
and variable 1 is `theta`. -/
def scaledResidualExprList : List Expr :=
  let phi := ev 0
  let theta := ev 1
  let one := ec 1
  let half := ec (1 / 2)
  let delta := esub theta phi
  let cp := ecos phi
  let sp := esin phi
  let ct := ecos theta
  let st := esin theta
  let base :=
    eadd
      (eadd (esub (esub (escale (1 / 2) epi) phi) theta)
        (escale (1 / 2) delta))
      (escale (1 / 4) (emul delta delta))
  let den := esub cp (emul (eadd one (escale (1 / 2) delta)) sp)
  let num :=
    eadd
      (eadd (eadd sp half) (eneg (escale (1 / 2) cp)))
      (emul base sp)
  let numB :=
    eadd (emul num (eadd one (escale (1 / 2) delta))) (emul base den)
  let r1 :=
    eadd
      (eadd
        (eadd
          (eadd
            (esub (emul num (esub ct cp)) (emul (escale 2 numB) sp))
            (emul (emul (esub delta one) ct) den))
          (eneg (emul st den)))
        (emul cp den))
      (emul sp den)
  let r2 :=
    eadd
      (eadd
        (eadd
          (eadd
            (esub (emul num (eadd (escale 3 st) sp))
              (emul (escale 2 numB) cp))
            (emul (emul (escale 3 (esub delta one)) st) den))
          (emul (escale 3 ct) den))
        (eneg (emul sp den)))
      (emul cp den)
  r1 :: r2 :: []

/-- Select one of the two scaled residual expressions for the angle system. -/
def scaledResidualExpr (i : Fin 2) : Expr :=
  scaledResidualExprList.getD i.1 (ec 0)

/-- Both ASTs belong to LeanCert's fully proved core and AD fragment. -/
theorem scaledResidualExpr_supported :
    ∀ i : Fin 2, ADConstSupported (scaledResidualExpr i) := by
  intro i
  apply checkADConstSupported_correct
  fin_cases i <;> decide
theorem scaledResidualExpr_eval_zero (phi theta : ℝ) :
    evalFin (scaledResidualExpr (0 : Fin 2)) ![phi, theta] =
      scaledResidualOne phi theta := by
  simp [scaledResidualExpr, scaledResidualExprList, scaledResidualOne, scaledB,
    angleNumerator, angleDenominator, bBase, angleDelta,
    eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
    evalFin, finEnv]; ring
theorem scaledResidualExpr_eval_one (phi theta : ℝ) :
    evalFin (scaledResidualExpr (1 : Fin 2)) ![phi, theta] =
      scaledResidualTwo phi theta := by
  simp [scaledResidualExpr, scaledResidualExprList, scaledResidualTwo, scaledB,
    angleNumerator, angleDenominator, bBase, angleDelta,
    eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
    evalFin, finEnv]; ring

/-- Rational interval environment for the two angle variables. -/
def angleIntervalEnv (phiI thetaI : IntervalRat) : IntervalEnv
  | 0 => phiI
  | 1 => thetaI
  | _ => default

/-- Executable test that an interval lies strictly on one side of zero. -/
def intervalExcludesZero (I : IntervalRat) : Bool :=
  decide (I.hi < 0 ∨ 0 < I.lo)

/-- The executable zero-exclusion test is sound over real interval
membership. -/
theorem intervalExcludesZero_sound (I : IntervalRat)
    (h : intervalExcludesZero I = true) : (0 : ℝ) ∉ I := by
  have hrat : I.hi < 0 ∨ 0 < I.lo := by
    exact of_decide_eq_true h
  intro hmem
  rw [IntervalRat.mem_def] at hmem
  rcases hrat with hhi | hlo
  · have hhi' : (I.hi : ℝ) < 0 := by exact_mod_cast hhi
    linarith
  · have hlo' : 0 < (I.lo : ℝ) := by exact_mod_cast hlo
    linarith

end PartE
end GerverSofa

end

end

end

section

/-!
# Part E04: finite-cover replay foundation

E03 supplied a sound, executable rejection theorem for one rational rectangle
in the `(phi, theta)` plane.  This module lifts that kernel to finite lists of
rectangles and states the exact two remaining data obligations:

1. a finite rejected cover of the physical angle triangle outside the angle
   projection of `Reduced.box`;
2. local reconstruction into `Reduced.box` inside that angle projection.

Their conjunction yields `TwoAngleEnclosureTarget` and therefore the exact
DeepMind-shaped uniqueness theorem.  No cover or local enclosure is assumed as
an axiom: both remain ordinary theorem arguments.

The module also replays one nontrivial pilot rectangle near the origin.  This
checks the complete path from rational cell data through LeanCert interval
evaluation to the no-common-zero theorem before the large cover is generated.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core
open LeanCert.Engine
open PartALeanCert

/-- Kernel-reducible interval evaluation for one smooth residual.  This uses
the already certified project-specialized interval for `pi`, avoiding the
generic named-constant normalization bottleneck in closed `decide` replays. -/
def scaledResidualKernelInterval (i : Fin 2)
    (phiI thetaI : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  kernelPointEvalCore (scaledResidualExpr i)
    (angleIntervalEnv phiI thetaI) cfg.taylorDepth

/-- Soundness of the kernel-reducible residual evaluator. -/
theorem scaledResidual_mem_kernelInterval (i : Fin 2)
    (phi theta : ℝ) (phiI thetaI : IntervalRat)
    (hphi : phi ∈ phiI) (htheta : theta ∈ thetaI)
    (cfg : EvalConfig := {}) :
    (if i = 0 then scaledResidualOne phi theta
      else scaledResidualTwo phi theta) ∈
      scaledResidualKernelInterval i phiI thetaI cfg := by
  let u : Fin 2 → ℝ := ![phi, theta]
  have henv : envMem (finEnv u) (angleIntervalEnv phiI thetaI) := by
    intro n
    rcases n with (_ | _ | n)
    · simpa [u, finEnv, angleIntervalEnv] using hphi
    · simpa [u, finEnv, angleIntervalEnv] using htheta
    · change finEnv u (Nat.succ (Nat.succ n)) ∈ (default : IntervalRat)
      rw [IntervalRat.mem_default]
      simp [finEnv]
  have hcore := eval_mem_kernelPointEvalCore
    (scaledResidualExpr_supported i) (finEnv u)
    (angleIntervalEnv phiI thetaI) henv cfg.taylorDepth
  change evalFin (scaledResidualExpr i) u ∈
    scaledResidualKernelInterval i phiI thetaI cfg at hcore
  fin_cases i
  · simpa [u, scaledResidualExpr_eval_zero] using hcore
  · simpa [u, scaledResidualExpr_eval_one] using hcore

/-- A rational rectangle in the two-angle plane. -/
structure AngleCell where
  /-- The rational interval for the first switching angle φ. -/
  phiI : IntervalRat
  /-- The rational interval for the second switching angle θ. -/
  thetaI : IntervalRat

namespace AngleCell

/-- Real point membership in a rational angle cell. -/
def Contains (cell : AngleCell) (phi theta : ℝ) : Prop :=
  phi ∈ cell.phiI ∧ theta ∈ cell.thetaI

/-- Executable E03 rejection test for a complete angle cell. -/
def rejected (cell : AngleCell) (cfg : EvalConfig := {}) : Bool :=
  intervalExcludesZero
      (scaledResidualKernelInterval (0 : Fin 2) cell.phiI cell.thetaI cfg) ||
    intervalExcludesZero
      (scaledResidualKernelInterval (1 : Fin 2) cell.phiI cell.thetaI cfg)

/-- A cell accepted by the executable checker contains no common zero of the
two smooth residuals. -/
theorem no_common_zero_of_rejected
    (cell : AngleCell) (phi theta : ℝ)
    (hmem : cell.Contains phi theta)
    (cfg : EvalConfig := {})
    (hreject : cell.rejected cfg = true) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  have hreject' :
      intervalExcludesZero
          (scaledResidualKernelInterval
            (0 : Fin 2) cell.phiI cell.thetaI cfg) = true ∨
        intervalExcludesZero
          (scaledResidualKernelInterval
            (1 : Fin 2) cell.phiI cell.thetaI cfg) = true := by
    simpa only [rejected, Bool.or_eq_true] using hreject
  rintro ⟨hzero1, hzero2⟩
  rcases hreject' with hreject' | hreject'
  · have hmem' := scaledResidual_mem_kernelInterval (0 : Fin 2)
      phi theta cell.phiI cell.thetaI hmem.1 hmem.2 cfg
    have hnot := intervalExcludesZero_sound _ hreject'
    apply hnot
    simpa [hzero1] using hmem'
  · have hmem' := scaledResidual_mem_kernelInterval (1 : Fin 2)
      phi theta cell.phiI cell.thetaI hmem.1 hmem.2 cfg
    have hnot := intervalExcludesZero_sound _ hreject'
    apply hnot
    simpa [hzero2] using hmem'

end AngleCell

/-! ## Pilot replay -/

end PartE
end GerverSofa

end

end

end

section

/-!
# Part E21F: local two-angle Krawczyk closure repair

The residual-only cover becomes inefficient close to the certified Gerver
zero.  This module replaces arbitrarily deep subdivision there by a single
two-dimensional contraction certificate on a deliberately wider rational
box.  The wide box contains both the exact projection of `Reduced.box` and
the complete unresolved E19 tail.

The resulting theorem identifies every smooth residual zero in the wide box
with the already certified Part A reduced solution.  A terminal composition
theorem therefore needs interval rejection only outside this wide local box.
-/

/-! ## Concrete two-dimensional contraction data -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core
open LeanCert.Engine
open PartALeanCert

/-- Local angle box containing the complete unresolved E20 tail and the exact
angle projection of `Reduced.box`.  E21F narrows the exploratory E21 box to
the region actually required by the recorded E20 extrema. -/
def localAngleX : Fin 2 → IntervalRat := ![
  ⟨391 / 10000, 157 / 4000, by norm_num⟩,
  ⟨68113 / 100000, 34069 / 50000, by norm_num⟩
]

/-- Rational center near the already certified Gerver zero. -/
def localAngleCenter : Fin 2 → ℚ := ![
  3917736479 / 100000000000,
  681301509383 / 1000000000000
]

/-- Rational approximation to the inverse Jacobian of the two scaled
residuals at `localAngleCenter`. -/
def localAngleY : Matrix (Fin 2) (Fin 2) ℚ := ![
  ![-2886 / 10000, -1481 / 10000],
  ![6267 / 10000, -27218 / 10000]
]

/-- The default interval-evaluation configuration for local angle certification. -/
def localAngleCfg : EvalConfig := {}

/-- Contraction constant used by the checked local uniqueness theorem. -/
def localAngleQ : ℚ := 3 / 10

/-- Enclose the preconditioned Newton derivative on the local two-angle box. -/
def localAnglePJ : Matrix (Fin 2) (Fin 2) IntervalRat :=
  preconditionedJacobian localAngleY
    (intervalJacobian scaledResidualExpr localAngleX localAngleCfg)

/-- Enclose the local Newton image using the certified contraction bound. -/
def localAngleImage (i : Fin 2) : IntervalRat :=
  imageEnclosureWithQ scaledResidualExpr localAngleX localAngleCenter
    localAngleY localAngleCfg localAngleQ i

theorem localAngleQ_nonneg : (0 : ℚ) ≤ localAngleQ := by
  norm_num [localAngleQ]

theorem localAngleQ_lt_one : localAngleQ < (1 : ℚ) := by
  norm_num [localAngleQ]

theorem localAngleCenter_mem :
    FinBoxMem (fun i : Fin 2 => (localAngleCenter i : ℝ)) localAngleX := by
  intro i
  fin_cases i <;>
    simp [localAngleCenter, localAngleX, IntervalRat.mem_def] <;>
    norm_num
theorem localAngle_bound_lt :
    intervalMatrixBound localAnglePJ < localAngleQ := by
  decide +kernel

theorem localAngle_bound_le :
    intervalMatrixBound localAnglePJ ≤ localAngleQ :=
  localAngle_bound_lt.le
theorem localAngle_image_zero_inside :
    intervalStrictInside (localAngleImage (0 : Fin 2))
      (localAngleX (0 : Fin 2)) = true := by
  decide +kernel
theorem localAngle_image_one_inside :
    intervalStrictInside (localAngleImage (1 : Fin 2))
      (localAngleX (1 : Fin 2)) = true := by
  decide +kernel

theorem localAngle_images_inside :
    ∀ i : Fin 2,
      intervalStrictInside (localAngleImage i) (localAngleX i) = true := by
  intro i
  fin_cases i
  · exact localAngle_image_zero_inside
  · exact localAngle_image_one_inside

/-- Kernel-checked existence and uniqueness of a common scaled-residual zero
throughout the complete wide local box. -/
theorem localAngle_unique_scaled :
    ∃! u, FinBoxMem u localAngleX ∧ SystemZero scaledResidualExpr u := by
  exact uniqueSystemZero_of_certified_contraction
    scaledResidualExpr scaledResidualExpr_supported
    localAngleX localAngleCenter localAngleCenter_mem
    localAngleY localAngleCfg localAngleQ
    localAngleQ_nonneg localAngleQ_lt_one
    (by simpa [localAnglePJ] using localAngle_bound_le)
    (by simpa [localAngleImage] using localAngle_images_inside)

/-! ## Semantic bridge to named angles and the Part A solution -/

/-- The two-angle cell corresponding to the certified local interval box. -/
def localAngleCell : AngleCell :=
  ⟨localAngleX (0 : Fin 2), localAngleX (1 : Fin 2)⟩

/-- Package the two switching angles as a two-coordinate real vector. -/
def localAngleVector (phi theta : ℝ) : Fin 2 → ℝ := ![phi, theta]

theorem localAngleVector_mem_iff (phi theta : ℝ) :
    FinBoxMem (localAngleVector phi theta) localAngleX ↔
      localAngleCell.Contains phi theta := by
  constructor
  · intro h
    exact ⟨by simpa [localAngleVector, localAngleCell] using h (0 : Fin 2),
      by simpa [localAngleVector, localAngleCell] using h (1 : Fin 2)⟩
  · rintro ⟨hphi, htheta⟩ i
    fin_cases i
    · simpa [localAngleVector, localAngleCell] using hphi
    · simpa [localAngleVector, localAngleCell] using htheta

theorem localAngleVector_systemZero_iff (phi theta : ℝ) :
    SystemZero scaledResidualExpr (localAngleVector phi theta) ↔
      scaledResidualOne phi theta = 0 ∧ scaledResidualTwo phi theta = 0 := by
  constructor
  · intro h
    constructor
    · have hzero := h (0 : Fin 2)
      change evalFin (scaledResidualExpr (0 : Fin 2))
        (localAngleVector phi theta) = 0 at hzero
      simpa [localAngleVector, scaledResidualExpr_eval_zero] using hzero
    · have hzero := h (1 : Fin 2)
      change evalFin (scaledResidualExpr (1 : Fin 2))
        (localAngleVector phi theta) = 0 at hzero
      simpa [localAngleVector, scaledResidualExpr_eval_one] using hzero
  · rintro ⟨hzeroOne, hzeroTwo⟩ i
    fin_cases i
    · change evalFin (scaledResidualExpr (0 : Fin 2))
        (localAngleVector phi theta) = 0
      simpa [localAngleVector, scaledResidualExpr_eval_zero] using hzeroOne
    · change evalFin (scaledResidualExpr (1 : Fin 2))
        (localAngleVector phi theta) = 0
      simpa [localAngleVector, scaledResidualExpr_eval_one] using hzeroTwo

/-- The reduced parameter tuple selected by the concrete uniqueness certificate. -/
def certifiedReducedSolution : Reduced.Params :=
  PartALeanCert.reducedCertifiedUniqueSolution.solution

theorem certifiedReducedSolution_mem :
    certifiedReducedSolution ∈ Reduced.box := by
  exact PartALeanCert.reducedCertifiedUniqueSolution.solution_mem

theorem certifiedReducedSolution_satisfies :
    Reduced.Equations certifiedReducedSolution := by
  exact PartALeanCert.reducedCertifiedUniqueSolution.satisfies

/-- The Part A solution's angle pair lies strictly inside the wide local
box, by exact rational endpoint comparison. -/
theorem certifiedAngles_mem_localAngleCell :
    localAngleCell.Contains
      certifiedReducedSolution.phi certifiedReducedSolution.theta := by
  have hp := certifiedReducedSolution_mem
  dsimp [Reduced.box, qR] at hp
  rcases hp with
    ⟨_haLo, _haHi, _hbLo, _hbHi,
      hphiLo, hphiHi, hthetaLo, hthetaHi⟩
  change
    certifiedReducedSolution.phi ∈ localAngleX (0 : Fin 2) ∧
      certifiedReducedSolution.theta ∈ localAngleX (1 : Fin 2)
  constructor
  · change
      (((391 / 10000 : ℚ) : ℝ) ≤ certifiedReducedSolution.phi ∧
        certifiedReducedSolution.phi ≤ ((157 / 4000 : ℚ) : ℝ))
    constructor
    · norm_num at hphiLo ⊢
      linarith
    · norm_num at hphiHi ⊢
      linarith
  · change
      (((68113 / 100000 : ℚ) : ℝ) ≤ certifiedReducedSolution.theta ∧
        certifiedReducedSolution.theta ≤ ((34069 / 50000 : ℚ) : ℝ))
    constructor
    · norm_num at hthetaLo ⊢
      linarith
    · norm_num at hthetaHi ⊢
      linarith

theorem certifiedAngles_mem_localAngleX :
    FinBoxMem
      (localAngleVector certifiedReducedSolution.phi
        certifiedReducedSolution.theta) localAngleX :=
  (localAngleVector_mem_iff _ _).2 certifiedAngles_mem_localAngleCell

theorem certifiedAngles_systemZero :
    SystemZero scaledResidualExpr
      (localAngleVector certifiedReducedSolution.phi
        certifiedReducedSolution.theta) := by
  have hdeep : DeepMindABPhiThetaSpec
      certifiedReducedSolution.a certifiedReducedSolution.b
      certifiedReducedSolution.phi certifiedReducedSolution.theta :=
    deepMindSpec_of_mem_reducedBox_and_equations
      certifiedReducedSolution_mem certifiedReducedSolution_satisfies
  have htwo : TwoAngleSpec
      certifiedReducedSolution.phi certifiedReducedSolution.theta :=
    (exists_deepMindSpec_iff_twoAngleSpec
      certifiedReducedSolution.phi certifiedReducedSolution.theta).1
      ⟨certifiedReducedSolution.a, certifiedReducedSolution.b, hdeep⟩
  have hscaled :=
    (twoAngleSpec_iff_scaledTwoAngleSpec
      certifiedReducedSolution.phi certifiedReducedSolution.theta).1 htwo
  rcases hscaled with ⟨_hdom, _hden, _hA, _hB, hzeroOne, hzeroTwo⟩
  exact (localAngleVector_systemZero_iff _ _).2 ⟨hzeroOne, hzeroTwo⟩

/-- Every smooth physical solution in the wide local cell reconstructs to
the already certified Part A solution and hence belongs to `Reduced.box`. -/
theorem reconstructedParams_mem_reducedBox_of_mem_localAngleCell
    {phi theta : ℝ} (hspec : ScaledTwoAngleSpec phi theta)
    (hlocal : localAngleCell.Contains phi theta) :
    reconstructedParams phi theta ∈ Reduced.box := by
  have hmem : FinBoxMem (localAngleVector phi theta) localAngleX :=
    (localAngleVector_mem_iff phi theta).2 hlocal
  have hzero : SystemZero scaledResidualExpr (localAngleVector phi theta) :=
    (localAngleVector_systemZero_iff phi theta).2
      ⟨hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩
  have heq :
      localAngleVector phi theta =
        localAngleVector certifiedReducedSolution.phi
          certifiedReducedSolution.theta :=
    localAngle_unique_scaled.unique ⟨hmem, hzero⟩
      ⟨certifiedAngles_mem_localAngleX, certifiedAngles_systemZero⟩
  have hphi : phi = certifiedReducedSolution.phi := by
    have h := congrFun heq (0 : Fin 2)
    simpa [localAngleVector] using h
  have htheta : theta = certifiedReducedSolution.theta := by
    have h := congrFun heq (1 : Fin 2)
    simpa [localAngleVector] using h
  have hdeep : DeepMindABPhiThetaSpec
      certifiedReducedSolution.a certifiedReducedSolution.b
      certifiedReducedSolution.phi certifiedReducedSolution.theta :=
    deepMindSpec_of_mem_reducedBox_and_equations
      certifiedReducedSolution_mem certifiedReducedSolution_satisfies
  have hA := a_eq_reconstructed_of_physical_and_equations hdeep.1 hdeep.2
  have hB := b_eq_reconstructed_of_physical_and_equations hdeep.1 hdeep.2
  rw [hphi, htheta]
  change reducedParams
      (reconstructedA certifiedReducedSolution.phi
        certifiedReducedSolution.theta)
      (reconstructedB certifiedReducedSolution.phi
        certifiedReducedSolution.theta)
      certifiedReducedSolution.phi certifiedReducedSolution.theta ∈ Reduced.box
  rw [← hA, ← hB]
  simpa [reducedParams] using certifiedReducedSolution_mem

/-! ## Terminal composition with rejection only outside the wide box -/

/-- Solutions in the local angle cell reconstruct into the reduced parameter box. -/
def WideLocalReconstructionEnclosureTarget : Prop :=
  ∀ phi theta : ℝ,
    ScaledTwoAngleSpec phi theta →
    localAngleCell.Contains phi theta →
    reconstructedParams phi theta ∈ Reduced.box

theorem wideLocalReconstructionEnclosureTarget :
    WideLocalReconstructionEnclosureTarget := by
  intro phi theta hspec hlocal
  exact reconstructedParams_mem_reducedBox_of_mem_localAngleCell hspec hlocal

/-! Machine-readable replay markers consumed by the E21 runner. -/

/- Exact diagnostic values are printed even if a later repair run stops at a
closed Boolean theorem. -/

end PartE
end GerverSofa

end

end

end

section

/-!
# Part E22F foundation: adaptive global cover

This module replaces the probe-only upper-wedge files by one kernel-reducible
adaptive checker.  Starting from the rational square `[0, 4/5]^2`, it prunes
cells which are outside the physical triangle, cells wholly contained in the
wide E21 local box, and cells rejected by the certified E03 interval kernel.
Every remaining cell is split into four exact rational children.  Depth 18 is
the depth reached by the final E20 refinement around the Gerver root.

The soundness theorem is independent of the closed computation.  E22F compiles
the depth-18 Boolean certificate in sixty-four independent depth-15 modules;
`ParallelAdaptiveGlobalCoverClosure` recombines them without recomputation.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core

/-- The rational midpoint of an angle interval. -/
def angleMid (i : IntervalRat) : ℚ := (i.lo + i.hi) / 2

/-- The closed lower half of a rational interval. -/
def intervalLow (i : IntervalRat) : IntervalRat :=
  ⟨i.lo, angleMid i, by
    dsimp [angleMid]
    linarith [i.le]⟩

/-- The closed upper half of a rational interval. -/
def intervalHigh (i : IntervalRat) : IntervalRat :=
  ⟨angleMid i, i.hi, by
    dsimp [angleMid]
    linarith [i.le]⟩

/-- Bisect both angle intervals and select the lower φ half and lower θ half. -/
def childLL (cell : AngleCell) : AngleCell :=
  ⟨intervalLow cell.phiI, intervalLow cell.thetaI⟩

/-- Bisect both angle intervals and select the lower φ half and upper θ half. -/
def childLH (cell : AngleCell) : AngleCell :=
  ⟨intervalLow cell.phiI, intervalHigh cell.thetaI⟩

/-- Bisect both angle intervals and select the upper φ half and lower θ half. -/
def childHL (cell : AngleCell) : AngleCell :=
  ⟨intervalHigh cell.phiI, intervalLow cell.thetaI⟩

/-- Bisect both angle intervals and select the upper φ half and upper θ half. -/
def childHH (cell : AngleCell) : AngleCell :=
  ⟨intervalHigh cell.phiI, intervalHigh cell.thetaI⟩

/-- A rational cell lies strictly above the physical half-plane `phi ≤ theta`.
The strict comparison deliberately keeps all cells touching the diagonal. -/
def physicallyIrrelevant (cell : AngleCell) : Bool :=
  decide (cell.thetaI.hi < cell.phiI.lo)

/-- Every point of the rational cell lies in the wide E21 local box. -/
def cellInsideLocal (cell : AngleCell) : Bool :=
  decide (
    localAngleCell.phiI.lo ≤ cell.phiI.lo ∧
    cell.phiI.hi ≤ localAngleCell.phiI.hi ∧
    localAngleCell.thetaI.lo ≤ cell.thetaI.lo ∧
    cell.thetaI.hi ≤ localAngleCell.thetaI.hi)

/-- Adaptive four-way replay.  A node closes when it is irrelevant, local, or
rejected.  Otherwise all four rational midpoint children must close. -/
def adaptiveCoverCheck : Nat → AngleCell → Bool
  | 0, cell =>
      if physicallyIrrelevant cell = true then true
      else if cellInsideLocal cell = true then true
      else cell.rejected
  | depth + 1, cell =>
      if physicallyIrrelevant cell = true then true
      else if cellInsideLocal cell = true then true
      else if cell.rejected = true then true
      else
        adaptiveCoverCheck depth (childLL cell) &&
          (adaptiveCoverCheck depth (childLH cell) &&
            (adaptiveCoverCheck depth (childHL cell) &&
              adaptiveCoverCheck depth (childHH cell)))

theorem physicallyIrrelevant_no_physical_point
    (cell : AngleCell) (phi theta : ℝ)
    (hirr : physicallyIrrelevant cell = true)
    (hdom : PhysicalAngleDomain phi theta)
    (hmem : cell.Contains phi theta) : False := by
  have hrat : cell.thetaI.hi < cell.phiI.lo := by
    exact of_decide_eq_true hirr
  have hreal : (cell.thetaI.hi : ℝ) < (cell.phiI.lo : ℝ) := by
    exact_mod_cast hrat
  change phi ∈ cell.phiI ∧ theta ∈ cell.thetaI at hmem
  simp only [IntervalRat.mem_def] at hmem
  linarith [hdom.2.1, hmem.1.1, hmem.2.2]

theorem cellInsideLocal_sound
    (cell : AngleCell) (phi theta : ℝ)
    (hlocal : cellInsideLocal cell = true)
    (hmem : cell.Contains phi theta) :
    localAngleCell.Contains phi theta := by
  have hb :
      localAngleCell.phiI.lo ≤ cell.phiI.lo ∧
      cell.phiI.hi ≤ localAngleCell.phiI.hi ∧
      localAngleCell.thetaI.lo ≤ cell.thetaI.lo ∧
      cell.thetaI.hi ≤ localAngleCell.thetaI.hi := by
    exact of_decide_eq_true hlocal
  change phi ∈ cell.phiI ∧ theta ∈ cell.thetaI at hmem
  change phi ∈ localAngleCell.phiI ∧ theta ∈ localAngleCell.thetaI
  simp only [IntervalRat.mem_def] at hmem ⊢
  have hpLo : (localAngleCell.phiI.lo : ℝ) ≤ (cell.phiI.lo : ℝ) := by
    exact_mod_cast hb.1
  have hpHi : (cell.phiI.hi : ℝ) ≤ (localAngleCell.phiI.hi : ℝ) := by
    exact_mod_cast hb.2.1
  have htLo : (localAngleCell.thetaI.lo : ℝ) ≤ (cell.thetaI.lo : ℝ) := by
    exact_mod_cast hb.2.2.1
  have htHi : (cell.thetaI.hi : ℝ) ≤ (localAngleCell.thetaI.hi : ℝ) := by
    exact_mod_cast hb.2.2.2
  exact ⟨⟨hpLo.trans hmem.1.1, hmem.1.2.trans hpHi⟩,
    ⟨htLo.trans hmem.2.1, hmem.2.2.trans htHi⟩⟩

/-- Every real point in a parent cell belongs to at least one of its four
closed midpoint children. -/
theorem contains_some_midpoint_child
    (cell : AngleCell) (phi theta : ℝ)
    (hmem : cell.Contains phi theta) :
    (childLL cell).Contains phi theta ∨
      (childLH cell).Contains phi theta ∨
      (childHL cell).Contains phi theta ∨
      (childHH cell).Contains phi theta := by
  change phi ∈ cell.phiI ∧ theta ∈ cell.thetaI at hmem
  simp only [IntervalRat.mem_def] at hmem
  by_cases hp : phi ≤ (angleMid cell.phiI : ℝ)
  · by_cases ht : theta ≤ (angleMid cell.thetaI : ℝ)
    · left
      change phi ∈ intervalLow cell.phiI ∧ theta ∈ intervalLow cell.thetaI
      simp only [IntervalRat.mem_def, intervalLow]
      exact ⟨⟨hmem.1.1, hp⟩, ⟨hmem.2.1, ht⟩⟩
    · right; left
      have ht' : (angleMid cell.thetaI : ℝ) ≤ theta :=
        le_of_lt (lt_of_not_ge ht)
      change phi ∈ intervalLow cell.phiI ∧ theta ∈ intervalHigh cell.thetaI
      simp only [IntervalRat.mem_def, intervalLow, intervalHigh]
      exact ⟨⟨hmem.1.1, hp⟩, ⟨ht', hmem.2.2⟩⟩
  · have hp' : (angleMid cell.phiI : ℝ) ≤ phi :=
      le_of_lt (lt_of_not_ge hp)
    by_cases ht : theta ≤ (angleMid cell.thetaI : ℝ)
    · right; right; left
      change phi ∈ intervalHigh cell.phiI ∧ theta ∈ intervalLow cell.thetaI
      simp only [IntervalRat.mem_def, intervalLow, intervalHigh]
      exact ⟨⟨hp', hmem.1.2⟩, ⟨hmem.2.1, ht⟩⟩
    · right; right; right
      have ht' : (angleMid cell.thetaI : ℝ) ≤ theta :=
        le_of_lt (lt_of_not_ge ht)
      change phi ∈ intervalHigh cell.phiI ∧ theta ∈ intervalHigh cell.thetaI
      simp only [IntervalRat.mem_def, intervalHigh]
      exact ⟨⟨hp', hmem.1.2⟩, ⟨ht', hmem.2.2⟩⟩

/-- Semantic soundness of the adaptive Boolean replay. -/
theorem adaptiveCoverCheck_no_common_zero
    (depth : Nat) (cell : AngleCell)
    (hcheck : adaptiveCoverCheck depth cell = true)
    (phi theta : ℝ)
    (hdom : PhysicalAngleDomain phi theta)
    (hmem : cell.Contains phi theta)
    (houtside : ¬ localAngleCell.Contains phi theta) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  induction depth generalizing cell with
  | zero =>
      by_cases hirr : physicallyIrrelevant cell = true
      · exact (physicallyIrrelevant_no_physical_point
          cell phi theta hirr hdom hmem).elim
      by_cases hlocal : cellInsideLocal cell = true
      · exact (houtside (cellInsideLocal_sound
          cell phi theta hlocal hmem)).elim
      have hrejected : cell.rejected = true := by
        simpa [adaptiveCoverCheck, hirr, hlocal] using hcheck
      exact AngleCell.no_common_zero_of_rejected
        cell phi theta hmem (cfg := {}) hrejected
  | succ depth ih =>
      by_cases hirr : physicallyIrrelevant cell = true
      · exact (physicallyIrrelevant_no_physical_point
          cell phi theta hirr hdom hmem).elim
      by_cases hlocal : cellInsideLocal cell = true
      · exact (houtside (cellInsideLocal_sound
          cell phi theta hlocal hmem)).elim
      by_cases hrejected : cell.rejected = true
      · exact AngleCell.no_common_zero_of_rejected
          cell phi theta hmem (cfg := {}) hrejected
      have hchildren :
          adaptiveCoverCheck depth (childLL cell) = true ∧
          (adaptiveCoverCheck depth (childLH cell) = true ∧
          (adaptiveCoverCheck depth (childHL cell) = true ∧
            adaptiveCoverCheck depth (childHH cell) = true)) := by
        simpa [adaptiveCoverCheck, hirr, hlocal, hrejected,
          Bool.and_eq_true] using hcheck
      rcases contains_some_midpoint_child cell phi theta hmem with
        hll | hlh | hhl | hhh
      · exact ih (cell := childLL cell) hchildren.1 hll
      · exact ih (cell := childLH cell) hchildren.2.1 hlh
      · exact ih (cell := childHL cell) hchildren.2.2.1 hhl
      · exact ih (cell := childHH cell) hchildren.2.2.2 hhh

/-- Rational root containing the complete physical angle triangle. -/
def globalAngleRoot : AngleCell :=
  ⟨⟨0, 4 / 5, by norm_num⟩, ⟨0, 4 / 5, by norm_num⟩⟩

theorem physicalAngleDomain_mem_globalAngleRoot
    (phi theta : ℝ) (hdom : PhysicalAngleDomain phi theta) :
    globalAngleRoot.Contains phi theta := by
  have hpi := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hpi.2
  have h32 : (ExactReplay.piI.hi : ℝ) < (16 / 5 : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  have htheta : theta < (4 / 5 : ℝ) := by
    linarith [hdom.2.2]
  change phi ∈ (⟨0, 4 / 5, by norm_num⟩ : IntervalRat) ∧
    theta ∈ (⟨0, 4 / 5, by norm_num⟩ : IntervalRat)
  simp only [IntervalRat.mem_def]
  norm_num at ⊢
  exact ⟨⟨hdom.1, (hdom.2.1.trans htheta.le)⟩,
    ⟨hdom.1.trans hdom.2.1, htheta.le⟩⟩

/-- A parent closes whenever its four children close.  This lemma permits the
depth-18 computation to be compiled in independent shards without changing
the kernel proposition that is certified. -/
theorem adaptiveCoverCheck_succ_of_children
    (depth : Nat) (cell : AngleCell)
    (hLL : adaptiveCoverCheck depth (childLL cell) = true)
    (hLH : adaptiveCoverCheck depth (childLH cell) = true)
    (hHL : adaptiveCoverCheck depth (childHL cell) = true)
    (hHH : adaptiveCoverCheck depth (childHH cell) = true) :
    adaptiveCoverCheck (depth + 1) cell = true := by
  by_cases hirr : physicallyIrrelevant cell = true
  · simp [adaptiveCoverCheck, hirr]
  by_cases hlocal : cellInsideLocal cell = true
  · simp [adaptiveCoverCheck, hirr, hlocal]
  by_cases hrejected : cell.rejected = true
  · simp [adaptiveCoverCheck, hirr, hlocal, hrejected]
  simp [adaptiveCoverCheck, hirr, hlocal, hrejected, hLL, hLH, hHL, hHH]

end PartE
end GerverSofa

end

end

end

section

/-!
# E24 aligned region foundation

Four rational rectangles are aligned exactly with the four sides of the
wide E21 local angle cell.  Their union covers every point of the global
physical angle root that is not in the local cell.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

/-- The exclusion root cell below the local φ interval, with `φ ≤ 391/10000`. -/
def e24PhiBelowRoot : AngleCell :=
  ⟨⟨0, 391 / 10000, by norm_num⟩,
    ⟨0, 4 / 5, by norm_num⟩⟩

/-- The exclusion root cell above the local φ interval, with `157/4000 ≤ φ`. -/
def e24PhiAboveRoot : AngleCell :=
  ⟨⟨157 / 4000, 4 / 5, by norm_num⟩,
    ⟨0, 4 / 5, by norm_num⟩⟩

/-- The exclusion root cell below the local θ interval, with `θ ≤ 68113/100000`. -/
def e24ThetaBelowRoot : AngleCell :=
  ⟨⟨0, 4 / 5, by norm_num⟩,
    ⟨0, 68113 / 100000, by norm_num⟩⟩

/-- The exclusion root cell above the local θ interval, with `34069/50000 ≤ θ`. -/
def e24ThetaAboveRoot : AngleCell :=
  ⟨⟨0, 4 / 5, by norm_num⟩,
    ⟨34069 / 50000, 4 / 5, by norm_num⟩⟩

end PartE
end GerverSofa

end

end

end

section

/-!
# E24 aligned-region semantic closure

This file contains no closed heavy computation.  It proves that the four
aligned rectangles cover the complement of the E21 local cell inside the
physical triangle and turns four Boolean adaptive-cover certificates into the
terminal DeepMind-shaped uniqueness theorem.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core

theorem e24AlignedRoots_cover_outside_local
    (phi theta : ℝ)
    (hdom : PhysicalAngleDomain phi theta)
    (houtside : ¬ localAngleCell.Contains phi theta) :
    e24PhiBelowRoot.Contains phi theta ∨
      e24PhiAboveRoot.Contains phi theta ∨
      e24ThetaBelowRoot.Contains phi theta ∨
      e24ThetaAboveRoot.Contains phi theta := by
  have hglobal :=
    physicalAngleDomain_mem_globalAngleRoot phi theta hdom
  change
    phi ∈ globalAngleRoot.phiI ∧ theta ∈ globalAngleRoot.thetaI at hglobal
  simp only [globalAngleRoot, IntervalRat.mem_def] at hglobal
  by_cases hpLo :
      phi ≤ (((391 / 10000 : ℚ) : ℝ))
  · left
    change
      phi ∈ e24PhiBelowRoot.phiI ∧ theta ∈ e24PhiBelowRoot.thetaI
    simp only [e24PhiBelowRoot, IntervalRat.mem_def]
    exact ⟨⟨hglobal.1.1, hpLo⟩, hglobal.2⟩
  by_cases hpHi :
      (((157 / 4000 : ℚ) : ℝ)) ≤ phi
  · right; left
    change
      phi ∈ e24PhiAboveRoot.phiI ∧ theta ∈ e24PhiAboveRoot.thetaI
    simp only [e24PhiAboveRoot, IntervalRat.mem_def]
    exact ⟨⟨hpHi, hglobal.1.2⟩, hglobal.2⟩
  by_cases htLo :
      theta ≤ (((68113 / 100000 : ℚ) : ℝ))
  · right; right; left
    change
      phi ∈ e24ThetaBelowRoot.phiI ∧ theta ∈ e24ThetaBelowRoot.thetaI
    simp only [e24ThetaBelowRoot, IntervalRat.mem_def]
    exact ⟨hglobal.1, ⟨hglobal.2.1, htLo⟩⟩
  by_cases htHi :
      (((34069 / 50000 : ℚ) : ℝ)) ≤ theta
  · right; right; right
    change
      phi ∈ e24ThetaAboveRoot.phiI ∧ theta ∈ e24ThetaAboveRoot.thetaI
    simp only [e24ThetaAboveRoot, IntervalRat.mem_def]
    exact ⟨hglobal.1, ⟨htHi, hglobal.2.2⟩⟩
  have hphiLo :
      (((391 / 10000 : ℚ) : ℝ)) < phi :=
    lt_of_not_ge hpLo
  have hphiHi :
      phi < (((157 / 4000 : ℚ) : ℝ)) :=
    lt_of_not_ge hpHi
  have hthetaLo :
      (((68113 / 100000 : ℚ) : ℝ)) < theta :=
    lt_of_not_ge htLo
  have hthetaHi :
      theta < (((34069 / 50000 : ℚ) : ℝ)) :=
    lt_of_not_ge htHi
  exfalso
  apply houtside
  change
    phi ∈ localAngleCell.phiI ∧ theta ∈ localAngleCell.thetaI
  constructor
  · change phi ∈ localAngleX (0 : Fin 2)
    simp only [localAngleX, IntervalRat.mem_def]
    exact ⟨hphiLo.le, hphiHi.le⟩
  · change theta ∈ localAngleX (1 : Fin 2)
    simp only [localAngleX, IntervalRat.mem_def]
    exact ⟨hthetaLo.le, hthetaHi.le⟩

theorem e24NoCommonZeroOutsideLocal_of_alignedChecks
    (hPhiBelow : adaptiveCoverCheck 14 e24PhiBelowRoot = true)
    (hPhiAbove : adaptiveCoverCheck 16 e24PhiAboveRoot = true)
    (hThetaBelow : adaptiveCoverCheck 18 e24ThetaBelowRoot = true)
    (hThetaAbove : adaptiveCoverCheck 19 e24ThetaAboveRoot = true)
    (phi theta : ℝ)
    (hdom : PhysicalAngleDomain phi theta)
    (houtside : ¬ localAngleCell.Contains phi theta) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  rcases e24AlignedRoots_cover_outside_local phi theta hdom houtside with
    hmem | hmem | hmem | hmem
  · exact adaptiveCoverCheck_no_common_zero
      14 e24PhiBelowRoot hPhiBelow phi theta hdom hmem houtside
  · exact adaptiveCoverCheck_no_common_zero
      16 e24PhiAboveRoot hPhiAbove phi theta hdom hmem houtside
  · exact adaptiveCoverCheck_no_common_zero
      18 e24ThetaBelowRoot hThetaBelow phi theta hdom hmem houtside
  · exact adaptiveCoverCheck_no_common_zero
      19 e24ThetaAboveRoot hThetaAbove phi theta hdom hmem houtside

theorem e24ScaledResidualEnclosureTarget_of_alignedChecks
    (hPhiBelow : adaptiveCoverCheck 14 e24PhiBelowRoot = true)
    (hPhiAbove : adaptiveCoverCheck 16 e24PhiAboveRoot = true)
    (hThetaBelow : adaptiveCoverCheck 18 e24ThetaBelowRoot = true)
    (hThetaAbove : adaptiveCoverCheck 19 e24ThetaAboveRoot = true) :
    ScaledResidualEnclosureTarget := by
  intro phi theta hspec
  by_cases hin : localAngleCell.Contains phi theta
  · exact wideLocalReconstructionEnclosureTarget phi theta hspec hin
  · have hnozero :=
      e24NoCommonZeroOutsideLocal_of_alignedChecks
        hPhiBelow hPhiAbove hThetaBelow hThetaAbove
        phi theta hspec.1 hin
    exact (hnozero ⟨hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩).elim

theorem deepMindABPhiTheta_existsUnique_of_alignedChecks
    (hPhiBelow : adaptiveCoverCheck 14 e24PhiBelowRoot = true)
    (hPhiAbove : adaptiveCoverCheck 16 e24PhiAboveRoot = true)
    (hThetaBelow : adaptiveCoverCheck 18 e24ThetaBelowRoot = true)
    (hThetaAbove : adaptiveCoverCheck 19 e24ThetaAboveRoot = true) :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 :=
  deepMindABPhiTheta_existsUnique_of_twoAngleEnclosure
    ((scaledResidualEnclosureTarget_iff_twoAngleEnclosureTarget).1
      (e24ScaledResidualEnclosureTarget_of_alignedChecks
        hPhiBelow hPhiAbove hThetaBelow hThetaAbove))

end PartE
end GerverSofa

end

end

end

section

/-!
# E24KC2 proof helpers

The discovery phase is intentionally outside the trusted chain.  It only chooses
where to stop splitting and which terminal reason to claim.

Every claimed leaf is then checked by the Lean kernel:
* physically irrelevant leaf -> `physicallyIrrelevant cell = true`;
* local leaf -> `cellInsideLocal cell = true`;
* interval-rejected leaf -> `cell.rejected = true`;
* unresolved frontier -> the old adaptive checker, but with remaining depth <= 9.

These lemmas lift a primitive terminal fact to an `adaptiveCoverCheck` fact at
arbitrary remaining depth without asking the kernel to explore the subtree.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

theorem adaptiveCoverCheck_true_of_physicallyIrrelevant
    (depth : Nat) (cell : AngleCell)
    (h : physicallyIrrelevant cell = true) :
    adaptiveCoverCheck depth cell = true := by
  cases depth <;> simp [adaptiveCoverCheck, h]

theorem adaptiveCoverCheck_true_of_rejected
    (depth : Nat) (cell : AngleCell)
    (h : cell.rejected = true) :
    adaptiveCoverCheck depth cell = true := by
  by_cases hirr : physicallyIrrelevant cell = true
  · cases depth <;> simp [adaptiveCoverCheck, hirr]
  · by_cases hlocal : cellInsideLocal cell = true
    · cases depth <;> simp [adaptiveCoverCheck, hirr, hlocal]
    · cases depth <;> simp [adaptiveCoverCheck, hirr, hlocal, h]

end PartE
end GerverSofa

end

end

end

section

/-! E24 kernel child certificate: PhiBelow/HL, remaining depth 13. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE
namespace CoverCertificateeccce3bad5

private abbrev cellRoot : AngleCell :=
  (childHL e24PhiBelowRoot)

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

private abbrev cell300 : AngleCell :=
  childLL cell30

private abbrev cell301 : AngleCell :=
  childLH cell30

private abbrev cell302 : AngleCell :=
  childHL cell30

private abbrev cell303 : AngleCell :=
  childHH cell30

private abbrev cell310 : AngleCell :=
  childLL cell31

private abbrev cell311 : AngleCell :=
  childLH cell31

private abbrev cell312 : AngleCell :=
  childHL cell31

private abbrev cell313 : AngleCell :=
  childHH cell31

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

private abbrev cell1130 : AngleCell :=
  childLL cell113

private abbrev cell1131 : AngleCell :=
  childLH cell113

private abbrev cell1132 : AngleCell :=
  childHL cell113

private abbrev cell1133 : AngleCell :=
  childHH cell113

private abbrev cell1310 : AngleCell :=
  childLL cell131

private abbrev cell1311 : AngleCell :=
  childLH cell131

private abbrev cell1312 : AngleCell :=
  childHL cell131

private abbrev cell1313 : AngleCell :=
  childHH cell131

private abbrev cell1330 : AngleCell :=
  childLL cell133

private abbrev cell1331 : AngleCell :=
  childLH cell133

private abbrev cell1332 : AngleCell :=
  childHL cell133

private abbrev cell1333 : AngleCell :=
  childHH cell133

private abbrev cell3110 : AngleCell :=
  childLL cell311

private abbrev cell3111 : AngleCell :=
  childLH cell311

private abbrev cell3112 : AngleCell :=
  childHL cell311

private abbrev cell3113 : AngleCell :=
  childHH cell311

private abbrev cell3130 : AngleCell :=
  childLL cell313

private abbrev cell3131 : AngleCell :=
  childLH cell313

private abbrev cell3132 : AngleCell :=
  childHL cell313

private abbrev cell3133 : AngleCell :=
  childHH cell313

private abbrev cell3310 : AngleCell :=
  childLL cell331

private abbrev cell3311 : AngleCell :=
  childLH cell331

private abbrev cell3312 : AngleCell :=
  childHL cell331

private abbrev cell3313 : AngleCell :=
  childHH cell331

private abbrev cell3330 : AngleCell :=
  childLL cell333

private abbrev cell3331 : AngleCell :=
  childLH cell333

private abbrev cell3332 : AngleCell :=
  childHL cell333

private abbrev cell3333 : AngleCell :=
  childHH cell333

private theorem checked1130 : adaptiveCoverCheck 9 cell1130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1130 (by decide +kernel)

private theorem checked1131 : adaptiveCoverCheck 9 cell1131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1131 (by decide +kernel)

private theorem checked1132 : adaptiveCoverCheck 9 cell1132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1132 (by decide +kernel)

private theorem checked1133 : adaptiveCoverCheck 9 cell1133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1133 (by decide +kernel)

private theorem checked1310 : adaptiveCoverCheck 9 cell1310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1310 (by decide +kernel)

private theorem checked1311 : adaptiveCoverCheck 9 cell1311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1311 (by decide +kernel)

private theorem checked1312 : adaptiveCoverCheck 9 cell1312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1312 (by decide +kernel)

private theorem checked1313 : adaptiveCoverCheck 9 cell1313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1313 (by decide +kernel)

private theorem checked1330 : adaptiveCoverCheck 9 cell1330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1330 (by decide +kernel)

private theorem checked1331 : adaptiveCoverCheck 9 cell1331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1331 (by decide +kernel)

private theorem checked1332 : adaptiveCoverCheck 9 cell1332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1332 (by decide +kernel)

private theorem checked1333 : adaptiveCoverCheck 9 cell1333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell1333 (by decide +kernel)

private theorem checked3110 : adaptiveCoverCheck 9 cell3110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3110 (by decide +kernel)

private theorem checked3111 : adaptiveCoverCheck 9 cell3111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3111 (by decide +kernel)

private theorem checked3112 : adaptiveCoverCheck 9 cell3112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3112 (by decide +kernel)

private theorem checked3113 : adaptiveCoverCheck 9 cell3113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3113 (by decide +kernel)

private theorem checked3130 : adaptiveCoverCheck 9 cell3130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3130 (by decide +kernel)

private theorem checked3131 : adaptiveCoverCheck 9 cell3131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3131 (by decide +kernel)

private theorem checked3132 : adaptiveCoverCheck 9 cell3132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3132 (by decide +kernel)

private theorem checked3133 : adaptiveCoverCheck 9 cell3133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3133 (by decide +kernel)

private theorem checked3310 : adaptiveCoverCheck 9 cell3310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3310 (by decide +kernel)

private theorem checked3311 : adaptiveCoverCheck 9 cell3311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3311 (by decide +kernel)

private theorem checked3312 : adaptiveCoverCheck 9 cell3312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3312 (by decide +kernel)

private theorem checked3313 : adaptiveCoverCheck 9 cell3313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3313 (by decide +kernel)

private theorem checked3330 : adaptiveCoverCheck 9 cell3330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3330 (by decide +kernel)

private theorem checked3331 : adaptiveCoverCheck 9 cell3331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3331 (by decide +kernel)

private theorem checked3332 : adaptiveCoverCheck 9 cell3332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3332 (by decide +kernel)

private theorem checked3333 : adaptiveCoverCheck 9 cell3333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3333 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 10 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 10 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 10 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 10 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 10 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 10 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 10 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 10 cell113 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell113
    checked1130 checked1131 checked1132 checked1133

private theorem checked120 : adaptiveCoverCheck 10 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 10 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 10 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 10 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 10 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 10 cell131 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell131
    checked1310 checked1311 checked1312 checked1313

private theorem checked132 : adaptiveCoverCheck 10 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 10 cell133 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell133
    checked1330 checked1331 checked1332 checked1333

private theorem checked300 : adaptiveCoverCheck 10 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 10 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 10 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 10 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 10 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 10 cell311 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell311
    checked3110 checked3111 checked3112 checked3113

private theorem checked312 : adaptiveCoverCheck 10 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 10 cell313 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell313
    checked3130 checked3131 checked3132 checked3133

private theorem checked320 : adaptiveCoverCheck 10 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 10 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 10 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 10 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 10 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 10 cell331 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell331
    checked3310 checked3311 checked3312 checked3313

private theorem checked332 : adaptiveCoverCheck 10 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 10 cell333 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell333
    checked3330 checked3331 checked3332 checked3333

private theorem checked00 : adaptiveCoverCheck 11 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 11 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 11 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 11 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 11 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 11 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 11 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 11 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 11 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 11 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 11 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 11 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 11 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 11 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 11 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 11 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 12 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 12 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 12 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 12 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 13 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 12 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateeccce3bad5

theorem e24PhiBelowKernelHL :
    adaptiveCoverCheck 13 (childHL e24PhiBelowRoot) = true := by
  exact CoverCertificateeccce3bad5.checkedRoot

end PartE
end GerverSofa

end

end

end
