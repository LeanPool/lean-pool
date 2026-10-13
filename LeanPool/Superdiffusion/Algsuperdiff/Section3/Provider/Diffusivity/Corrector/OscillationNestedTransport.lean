/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicReplaceForcing

/-!
# OscillationNestedTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Moving the weak equation from the coarse cube to every finer concentric cube

The nested-recentring route of `OscillationTelescope` builds one harmonic
replacement per scale: on each cube `U_j = z + cu_{n+j}` of the concentric family
it subtracts from the corrector `w` the `H^1_0(U_j)` potential of the forcing.
The construction (`HarmonicReplaceForcing`) needs the weak equation
`int <grad w, grad psi> = int <G, grad psi>` **on `U_j`**, tested against
`H^1_0(U_j)`, whereas the corrector solves its equation only on the coarse cube
`U_N`, tested against the larger class `H^1_0(U_N)`.

The passage is a restriction of the test class along the extension by zero.  It
is already available inside CoarseGraining, in the solenoidality language:
CoarseGraining's `IsSolenoidalOn U g` is literally "`int_U <g, grad phi> = 0`
for every `phi in H^1_0(U)`", and
`Homogenization.IsSolenoidalOn.restrict_of_isOpen_of_memVectorL2` restricts it
to any open subset with `L^2` control there.  Its proof is the
extension-by-zero argument in the only form that is needed: a smooth test
function supported in the subdomain is already a legal test function upstairs,
and the two set integrals agree because the integrand vanishes off the support.

So no new Sobolev extension operator has to be built.  What this module
supplies is the translation between the two shapes -- the manuscript writes an
equation with a right-hand side, CoarseGraining's predicate is homogeneous --
and the specialization to the concentric cube family, packaged so that the
per-scale harmonic replacement can be produced directly from the coarse
equation.

## Contents

* `memVectorL2_mono` -- `L^2` control passes to subsets.
* `forall_h10Function_integral_vecDot_grad_eq_of_subset` -- **the transport**:
  the weak equation with right-hand side, moved to an open subset.
* `exists_h10Function_isWeaklyHarmonicOn_sub_sqrt_le_subcube` -- the per-scale
  harmonic replacement on a finer concentric cube, produced from the equation on
  the coarse one, with the birth-scale defect bound `sqrt d * M * 3^{m'}`.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the harmonic/oscillation layer of this same
directory.  It mentions no object of the manuscript: no model, no cutoff, no
shell, no corrector, no `sigmaBar`.  It is intended to be portable into
CoarseGraining by a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- Square integrability on a set passes to subsets. -/
theorem memVectorL2_mono {U V : Set (Vec d)} (hVU : V ⊆ U) {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) : MemVectorL2 V f :=
  hf.mono_measure (Measure.restrict_mono hVU le_rfl)

/-- **Transport of the weak equation to an open subset.**

If a field `A` solves `int_U <A, grad psi> = int_U <G, grad psi>` against every
`H^1_0(U)` competitor, then it solves the same equation on every open subset `V`
of `U` against every `H^1_0(V)` competitor.

The proof rewrites the equation as the solenoidality of `A - G`, applies
CoarseGraining's restriction of solenoidality along the extension by zero, and
splits the pairing back into its two halves. -/
theorem forall_h10Function_integral_vecDot_grad_eq_of_subset {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [IsFiniteMeasure (volumeMeasureOn V)] {A G : Vec d → Vec d}
    (hA : MemVectorL2 U A) (hG : MemVectorL2 U G)
    (hw : ∀ ψ : H10Function U,
      ∫ x in U, vecDot (A x) (ψ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x) (ψ.toH1Function.grad x) ∂volume) :
    ∀ ψ : H10Function V,
      ∫ x in V, vecDot (A x) (ψ.toH1Function.grad x) ∂volume =
        ∫ x in V, vecDot (G x) (ψ.toH1Function.grad x) ∂volume := by
  have hAV : MemVectorL2 V A := memVectorL2_mono hVU hA
  have hGV : MemVectorL2 V G := memVectorL2_mono hVU hG
  have hDV : MemVectorL2 V (fun x => A x - G x) := hAV.sub hGV
  have hsolU : IsSolenoidalOn U (fun x => A x - G x) := by
    intro φ
    have h₁ : IntegrableOn (fun x => vecDot (A x) (φ.toH1Function.grad x)) U volume :=
      integrableOn_vecDot_of_memVectorL2 hA φ.toH1Function.grad_memVectorL2
    have h₂ : IntegrableOn (fun x => vecDot (G x) (φ.toH1Function.grad x)) U volume :=
      integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
    have hpt : ∀ x : Vec d, vecDot (A x - G x) (φ.toH1Function.grad x) =
        vecDot (A x) (φ.toH1Function.grad x) -
          vecDot (G x) (φ.toH1Function.grad x) := fun x => vecDot_sub_left' _ _ _
    simp only [hpt]
    rw [integral_sub h₁ h₂, hw φ, sub_self]
  have hsolV : IsSolenoidalOn V (fun x => A x - G x) :=
    hsolU.restrict_of_isOpen_of_memVectorL2 hU hV hVU hDV
  intro ψ
  have h₁ : IntegrableOn (fun x => vecDot (A x) (ψ.toH1Function.grad x)) V volume :=
    integrableOn_vecDot_of_memVectorL2 hAV ψ.toH1Function.grad_memVectorL2
  have h₂ : IntegrableOn (fun x => vecDot (G x) (ψ.toH1Function.grad x)) V volume :=
    integrableOn_vecDot_of_memVectorL2 hGV ψ.toH1Function.grad_memVectorL2
  have hzero := hsolV ψ
  have hpt : ∀ x : Vec d, vecDot (A x - G x) (ψ.toH1Function.grad x) =
      vecDot (A x) (ψ.toH1Function.grad x) -
        vecDot (G x) (ψ.toH1Function.grad x) := fun x => vecDot_sub_left' _ _ _
  simp only [hpt] at hzero
  rw [integral_sub h₁ h₂, sub_eq_zero] at hzero
  exact hzero

/-- **The per-scale harmonic replacement on a finer concentric cube.**

Let `w` be an `H^1` function on the cube `z + cu_m` which weakly solves
`- Delta w = div G` there, and let `m' <= m`.  Then the restriction of `w` to the
concentric cube `z + cu_{m'}` admits a harmonic replacement whose gradient defect
has normalized `L^2` size at most `sqrt d * M * 3^{m'}` on that cube, `M` being a
bound for the differentials of the coordinates of the forcing.

This is the birth-scale atom of `HarmonicReplaceForcing`, made available at every
scale of the concentric family from the single equation on the coarse cube. -/
theorem exists_h10Function_isWeaklyHarmonicOn_sub_sqrt_le_subcube [NeZero d]
    (z : Vec d) {m m' : ℤ} (hmm : m' ≤ m) (w : H1Function (openCubeAtScale z m))
    {G : Vec d → Vec d} {M : ℝ} (hM : 0 ≤ M)
    (hGdiff : ∀ i : Fin d, Differentiable ℝ fun y => G y i)
    (hGbound : ∀ x ∈ openCubeAtScale z m, ∀ i : Fin d,
      ‖fderiv ℝ (fun y => G y i) x‖ ≤ M)
    (hw : ∀ ψ : H10Function (openCubeAtScale z m),
      ∫ x in openCubeAtScale z m, vecDot (w.grad x) (ψ.toH1Function.grad x) ∂volume =
        ∫ x in openCubeAtScale z m, vecDot (G x) (ψ.toH1Function.grad x) ∂volume) :
    ∃ φ : H10Function (openCubeAtScale z m'),
      IsWeaklyHarmonicOn (openCubeAtScale z m')
          ((w.restrict (isOpen_openCubeAtScale z m')
            (openCubeAtScale_subset_of_le z hmm) - φ.toH1Function).toFun) ∧
        Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m')
            φ.toH1Function.grad 0) ≤ Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ m' := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeAtScale z m')) :=
    isFiniteMeasure_restrict.mpr (volume_openCubeAtScale_ne_top z m')
  have hsub : openCubeAtScale z m' ⊆ openCubeAtScale z m :=
    openCubeAtScale_subset_of_le z hmm
  have hGm : MemVectorL2 (openCubeAtScale z m) G :=
    memVectorL2_of_differentiable_coord_openCubeAtScale hGdiff z m
  have hwrestrict := forall_h10Function_integral_vecDot_grad_eq_of_subset
    (isOpen_openCubeAtScale z m) (isOpen_openCubeAtScale z m') hsub
    w.grad_memVectorL2 hGm hw
  exact exists_h10Function_isWeaklyHarmonicOn_sub_sqrt_le z m'
    (w.restrict (isOpen_openCubeAtScale z m') hsub) hM hGdiff
    (fun x hx i => hGbound x (hsub hx) i) hwrestrict

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
