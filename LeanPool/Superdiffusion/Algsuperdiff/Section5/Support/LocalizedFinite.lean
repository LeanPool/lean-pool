/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.EssentialSupremum
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RepresentativeComparator

/-!
# LocalizedFinite

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The normalized forcing class, the localized quantities, and the good cube event

Section 5.1 attaches to each cube `y + □_n` two quantities: the localized error
`E`, comparing the rough-field solution with the comparator in the `L^∞` norm,
and the localized regularity `X`, the normalized `1/2`-Hölder seminorm of the
rough-field solution.  Both are suprema over the *normalized* forcing class
`[g]_{W^{1/2,∞}(y+□_n)} ≤ 1`.

The two quantities read a solution differently, and the difference is the
source's.  The `L^∞` norm is an essential supremum: it is insensitive to a null
set, so it is taken of the `H¹` functions themselves, with no representative and
no side condition that could drop a datum.  The `1/2`-Hölder seminorm is a
pointwise quantity, so it is taken of a continuous representative; the
representative is quantified by an *infimum*, which is the seminorm of the
unique continuous representative where one exists and `⊤` where none does.  A
solution too rough to have a continuous representative therefore makes `X`
infinite instead of contributing nothing.

The values are `ℝ≥0∞`, so an unbounded family has the value `⊤` rather than
collapsing.

## Main definitions

* `NormalizedForceAt y n g` — the normalization `[g]_{W^{1/2,∞}(y+□_n)} ≤ 1`.
* `IsCubeRepresentative y n u uRep` — `uRep` is a representative of `u`
  continuous on `y + □_n`.
* `localizedError`, `localizedRegularity` — the two quantities.
* `goodCubeEvent` — `{E ≤ ε} ∩ {X ≤ 2 Creg}`.

## References

* ABK26, the localized error and regularity quantities and the good cube event
  of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The normalized forcing class -/

/-- **The normalized forcing class of `y + □_n`**: the explicit two-point form of
`[g]_{W^{1/2,∞}(y+□_n)} ≤ 1`. -/
def NormalizedForceAt (y : Vec d) (n : ℤ) (g : Vec d → Vec d) : Prop :=
  HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (Real.rpow 3 (-(n : ℝ) / 2)) g

theorem normalizedForceAt_def {y : Vec d} {n : ℤ} {g : Vec d → Vec d} :
    NormalizedForceAt y n g ↔
      HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (Real.rpow 3 (-(n : ℝ) / 2)) g :=
  Iff.rfl

/-! ## 2. Continuous representatives as an explicit witness -/

/-- **`uRep` is a representative of `u` continuous on `y + □_n`.**  Finiteness of
its `1/2`-Hölder seminorm is deliberately *not* required: the source takes that
seminorm of the continuous representative, and an infinite value there is a
value of the localized regularity, not a reason to drop the datum. -/
def IsCubeRepresentative (y : Vec d) (n : ℤ) (u : H1Function (cubeSetAt y n))
    (uRep : Vec d → ℝ) : Prop :=
  uRep =ᵐ[volume.restrict (cubeSetAt y n)] u.toFun ∧
    ContinuousOn uRep (cubeSetAt y n)

/-- **Representatives of almost-everywhere equal solutions agree everywhere on
the cube.**  With the almost-everywhere uniqueness of the localized Dirichlet
problem this makes every pointwise quantity below independent of the choice of
solution and of representative. -/
theorem isCubeRepresentative_eqOn {y : Vec d} {n : ℤ}
    {u u' : H1Function (cubeSetAt y n)} {uRep u'Rep : Vec d → ℝ}
    (h : u.toFun =ᵐ[volume.restrict (cubeSetAt y n)] u'.toFun)
    (h₁ : IsCubeRepresentative y n u uRep) (h₂ : IsCubeRepresentative y n u' u'Rep) :
    Set.EqOn uRep u'Rep (cubeSetAt y n) :=
  eqOn_of_ae_eq_of_continuousOn (isOpen_cubeSetAt y n)
    ((h₁.1.trans h).trans h₂.1.symm) h₁.2 h₂.2

/-! ## 3. The two localized quantities -/

/-- **Continuous representatives on the open cube are unique.**  Two
representatives of the same `H¹` witness agree at every point of the cube. -/
theorem isCubeRepresentative_unique {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} {uRep u'Rep : Vec d → ℝ}
    (h₁ : IsCubeRepresentative y n u uRep) (h₂ : IsCubeRepresentative y n u u'Rep) :
    Set.EqOn uRep u'Rep (cubeSetAt y n) :=
  isCubeRepresentative_eqOn (Filter.EventuallyEq.refl _ _) h₁ h₂

/-- **The infimum over the continuous representatives of a witness is the value
at any one of them.**  By uniqueness the family is a singleton where it is
nonempty, so the infimum records the seminorm of the continuous representative
where there is one and `⊤` where there is none. -/
theorem iInf_isCubeRepresentative_holderSeminormOn {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} {uRep : Vec d → ℝ}
    (huRep : IsCubeRepresentative y n u uRep) (c : ℝ≥0∞) :
    (⨅ r : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u r,
        c * holderSeminormOn (cubeSetAt y n) (1 / 2) r) =
      c * holderSeminormOn (cubeSetAt y n) (1 / 2) uRep := by
  refine le_antisymm (iInf_le_of_le uRep (iInf_le _ huRep))
    (le_iInf fun r => le_iInf fun hr => ?_)
  rw [holderSeminormOn_eq_of_hasCubeContinuousRepresentativeAt huRep.1 huRep.2 hr.1 hr.2]

/-- **The localized error `E(y+□_n)`**: the supremum, over the normalized forcing
class and over the solutions of the two problems, of
`σ_n 3^{-n} ‖u_n - v‖_{L^∞(y+□_n)}`.

The `L^∞` norm is the essential supremum on the cube, of the `H¹` functions
themselves.  It does not see a null set, so it needs no representative and
carries no side condition; both inner families are nonempty by the solvability
of the two problems, and the value does not depend on which solutions are chosen
by their almost-everywhere uniqueness. -/
def localizedError (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ⨆ g : Vec d → Vec d, ⨆ _ : NormalizedForceAt y n g,
  ⨆ u : H1Function (cubeSetAt y n),
  ⨆ _ : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u g,
  ⨆ v : H1Function (cubeSetAt y n),
  ⨆ _ : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g,
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
      eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n))

/-- **The localized regularity `X(y+□_n)`**: the supremum, over the normalized
forcing class and over the rough-field solutions, of
`σ_n 3^{-n/2} [u_n]_{C^{0,1/2}(y+□_n)}`, the seminorm being that of the
continuous representative.

The representative is quantified by an infimum: it is unique where it exists, so
the infimum is its seminorm there, and it is `⊤` where no continuous
representative exists. -/
def localizedRegularity (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ⨆ g : Vec d → Vec d, ⨆ _ : NormalizedForceAt y n g,
  ⨆ u : H1Function (cubeSetAt y n),
  ⨆ _ : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u g,
  ⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
      holderSeminormOn (cubeSetAt y n) (1 / 2) uRep

/-- **The `L^∞` norm of the difference of two witnesses is the supremum norm of
the difference of their continuous representatives.**  This is how the localized
error, an essential supremum, is read pointwise where representatives exist. -/
theorem eLpNorm_top_sub_eq_supNormOn_sub {y : Vec d} {n : ℤ}
    {u v : H1Function (cubeSetAt y n)} {uRep vRep : Vec d → ℝ}
    (huRep : IsCubeRepresentative y n u uRep) (hvRep : IsCubeRepresentative y n v vRep) :
    eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) =
      supNormOn (cubeSetAt y n) fun x => uRep x - vRep x := by
  refine eLpNorm_top_restrict_eq_supNormOn_of_ae (isOpen_cubeSetAt y n) ?_
    (huRep.2.sub hvRep.2)
  filter_upwards [huRep.1, hvRep.1] with x hx hx'
  show uRep x - vRep x = u.toFun x - v.toFun x
  rw [hx, hx']

theorem le_localizedError (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d} (hg : NormalizedForceAt y n g)
    {u v : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u g)
    (hv : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g) :
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) ≤
      localizedError M n y omega :=
  le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le u (le_iSup_of_le hu
    (le_iSup_of_le v (le_iSup_of_le hv le_rfl)))))

theorem localizedError_le_iff {M : ABKModel d} {n : ℤ} {y : Vec d}
    {omega : Cutoff.CutoffSample d} {c : ℝ≥0∞} :
    localizedError M n y omega ≤ c ↔
      ∀ g : Vec d → Vec d, NormalizedForceAt y n g →
        ∀ u : H1Function (cubeSetAt y n),
          IsDirichletSolutionAt
            ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u g →
          ∀ v : H1Function (cubeSetAt y n),
            IsDirichletSolutionAt
              (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g →
            ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
                eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
                  (volume.restrict (cubeSetAt y n)) ≤ c := by
  simp only [localizedError, iSup_le_iff]

theorem localizedRegularity_le_iff {M : ABKModel d} {n : ℤ} {y : Vec d}
    {omega : Cutoff.CutoffSample d} {c : ℝ≥0∞} :
    localizedRegularity M n y omega ≤ c ↔
      ∀ g : Vec d → Vec d, NormalizedForceAt y n g →
        ∀ u : H1Function (cubeSetAt y n),
          IsDirichletSolutionAt
            ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u g →
          (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
              ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
                holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) ≤ c := by
  simp only [localizedRegularity, iSup_le_iff]

/-! ## 4. The good cube event -/

/-- **The good cube event `𝒢(y+□_n, ε)`**: the localized error does not exceed
`ε` and the localized regularity does not exceed `2 Creg`. -/
def goodCubeEvent (M : ABKModel d) (Creg : ℝ) (n : ℤ) (y : Vec d) (ep : ℝ) :
    Set (Cutoff.CutoffSample d) :=
  {omega | localizedError M n y omega ≤ ENNReal.ofReal ep} ∩
    {omega | localizedRegularity M n y omega ≤ ENNReal.ofReal (2 * Creg)}

/-! ## 6. Uniform bounds on the normalized class -/

/-- A uniform supremum bound for the representatives of the comparator, over the
whole normalized forcing class. -/
def HasUniformComparatorSupBound (M : ABKModel d) (n : ℤ) (y : Vec d) (Kcomp : ℝ) : Prop :=
  ∀ g : Vec d → Vec d, NormalizedForceAt y n g →
    ∀ v : H1Function (cubeSetAt y n),
      IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g →
      ∀ vRep : Vec d → ℝ, IsCubeRepresentative y n v vRep →
        supNormOn (cubeSetAt y n) vRep ≤ ENNReal.ofReal Kcomp

end

end Algsuperdiff.Section5.Support
