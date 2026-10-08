/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuAdmissibility

/-!
# High-contrast homogenization: Consistency.Dissolution

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finiteness of the competitor energies: the coarse response is an honest infimum

This module checks the definition of the coarse block response: the paper's
`𝐀(U; a)`, in Lean the sampling response `coarseBlock U a`, is computed from the
variational quantity `Mu U Q a`, the infimum over the admissible states `X` of
the competitor averages `volumeAverage U (blockEnergyDensity a X)`.

That average carries a junk value on non-integrable integrands.  Were the check
to fail, an admissible competitor could leave the block energy density
non-integrable, the Bochner integral would return its junk value, and the
infimum defining `Mu` — hence the response `𝐀(U; a)` — would be `0` for a
reason unrelated to the field, not the paper's variational value.  The
positive-definiteness statements written for the response, among them the
well-formedness the annealed contrast `Θ_m` of `e.Theta.m` presupposes, would
then be statements about a different object.

This module is a consistency check of that definition and is not a result of the
paper.

This file removes the junk branch from the definition: on every bounded
measurable cell, *every* admissible competitor of the coarse variational problem
has finite energy, for *every* field of the coefficient space.

The mechanism is the local uniform ellipticity built into the coefficient space.
A sample field has a measurable representative that is uniformly elliptic at
every point of the cell, with the constants the cell's boundedness supplies; the
deterministic theory turns admissibility into the energy-integrability package
for that representative, and the energy density only sees the almost everywhere
class of the field.  Consequently the junk value of the Bochner average is never
attained and `𝐀(U; a)` is the honest infimum of the energy over the admissible
class.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- On a field with a pointwise uniformly elliptic representative, every
admissible competitor of the coarse variational problem has finite energy, so
the junk branch of the Bochner average is unreachable and the coarse response is
the honest infimum. -/
theorem integrableOn_blockEnergyDensity_of_representative
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffSpace d} {f : CoeffField d} {lam Lam : ℝ}
    (hf : (⇑a.1 : Vec d → Mat d) =ᵐ[volume] f)
    (hEll : IsEllipticFieldOn lam Lam U f)
    {Q : BlockVec d} {X : BlockState d} (hX : IsBlockMuAdmissible U Q X) :
    IntegrableOn (blockEnergyDensity (⇑a.1) X) U volume := by
  have hInt := (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn
    (a := f) hEll).energyIntegrable
  refine hInt.congr ?_
  filter_upwards [ae_restrict_of_ae hf] with x hx
  simp only [blockEnergyDensity, blockCoeffField, hx]

/-- **The dissolution of the junk branch**, unconditionally on the coefficient
space: on every bounded measurable cell, every admissible competitor of the
coarse variational problem has finite energy.  The junk value of the Bochner
average is therefore never attained, and the coarse response `𝐀(U; a)` of the
variational definition is the honest infimum. -/
theorem integrableOn_blockEnergyDensity_coeffSpace
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure (volumeMeasureOn U)]
    (a : CoeffSpace d) {Q : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible U Q X) :
    IntegrableOn (blockEnergyDensity (⇑a.1) X) U volume := by
  obtain ⟨lam, Lam, f, hlam, hle, hfm, hfp, hfa⟩ :=
    exists_pointwise_elliptic_representative a.2 hUb
  refine integrableOn_blockEnergyDensity_of_representative (lam := lam)
    (Lam := Lam) hfa ⟨?_, hfp⟩ hX
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  exact Measurable.ite hU
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm)))
    measurable_const

end

end HighContrast
end HCPolySupport
