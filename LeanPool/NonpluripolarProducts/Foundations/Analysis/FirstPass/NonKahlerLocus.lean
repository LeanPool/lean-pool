/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold

/-!
# Lelong numbers, Kähler currents and the non-Kähler locus

Source: Copy-4, `sec:nK` and the introduction preceding `thm:main`
(`transcendental-nakamaye-copy4-20260911`).

This file introduces the definitions needed to state the analytic main theorem:

* `lelongNumber u x`: the Lelong number of an extended-real potential at `x`,
  computed in the preferred holomorphic chart at `x` as
  `sup {γ ≥ 0 : u ≤ γ log ‖z - x‖ + O(1)` on a punctured neighbourhood`}`.
  For quasi-plurisubharmonic `u` this is the logarithmic coefficient in
  [Demailly, III.6.9(e)](https://www-fourier.univ-grenoble-alpes.fr/~demailly/source_files/analgeom/agbook.pdf#page=165).
  With Xia's normalization of `ddᶜ`, that coefficient is twice Demailly's Lelong number
  of the associated current `θ + ddᶜ u` for smooth `θ`. For `u(z) = log ‖z‖²` on the line,
  the coefficient is 2 and the associated Dirac current has Lelong number 1 in Demailly's
  convention. This definition uses the preferred chart.
* `KahlerCurrent alpha`: a Kähler current in the Bott--Chern class `alpha`,
  presented as `θ + ddᶜ u` with `θ` a closed smooth representative, together
  with a Kähler form `ω'` with `θ + ddᶜ u ≥ ω'`.  Dominating some Kähler form
  is the manuscript's condition `T ≥ δ ω` on a compact Kähler manifold.  The
  presentation by a global quasi-psh potential is the standard
  `ddᶜ`-lemma description of closed `(1,1)`-currents in a fixed class; unlike
  `PresentedNonNefLocus.PresentedKahlerCurrent`, no analytic-singularity
  restriction is imposed.
* `nonKahlerLocus alpha` (`E_nK(α)`): the common positive-Lelong-number set of
  all Kähler currents in `alpha`.  When the class contains no Kähler current
  this intersection is the whole manifold, which is exactly the manuscript's
  convention `E_nK(α) = X` for pseudoeffective non-big classes.
* `nonNefLocus omega alpha` (`E_nn(α)`): the union over `ε > 0` of
  `E_nK(α + ε{ω})`.
* `IsIrreducibleComponent V S`: `V` is a maximal closed irreducible analytic
  subvariety contained in `S`.

These are new definitions of this first pass and are recorded in the
blueprint (`ana:geometric-setting`).  No property of them is asserted here
beyond unfolding lemmas.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal NNReal ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

noncomputable section

open PositiveClasses NumericalRestrictedVolumeScaffold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The Lelong number of an extended-real potential at `x`, in the preferred
holomorphic chart at `x`:
`ν(u, x) = sup {γ ≥ 0 : ∃ C, u(y) ≤ γ log ‖y - x‖ + C` for `y ≠ x` near `x`}. -/
def lelongNumber (u : M → EReal) (x : M) : ℝ≥0∞ :=
  ⨆ (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
      u y ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
          EReal)),
    (γ : ℝ≥0∞)

/-- A Kähler current `θ + ddᶜ u` in the class `alpha`: it dominates the Kähler
form `lowerBound`. -/
structure KahlerCurrent (alpha : RealBottChern n M) where
  /-- The smooth closed representative of the Bott–Chern class. -/
  representative : ClosedRealOneOneForm n M
  represents : RealBottChern.ofRepresentative representative = alpha
  /-- The potential perturbing the representative. -/
  potential : M → EReal
  /-- The Kähler background used as a lower bound. -/
  lowerBound : KahlerBackground n M
  strictlyPsh :
    IsThetaPshPotential (representative - lowerBound.form).val potential

/-- A class is big when it contains a Kähler current. -/
def IsBigClass (alpha : RealBottChern n M) : Prop :=
  Nonempty (KahlerCurrent alpha)

/-- The non-Kähler locus `E_nK(α)`: points where every Kähler current in the
class has positive Lelong number. -/
def nonKahlerLocus (alpha : RealBottChern n M) : Set M :=
  {x | ∀ T : KahlerCurrent alpha, 0 < lelongNumber (n := n) T.potential x}

@[simp] theorem mem_nonKahlerLocus {alpha : RealBottChern n M} {x : M} :
    x ∈ nonKahlerLocus alpha ↔
      ∀ T : KahlerCurrent alpha, 0 < lelongNumber (n := n) T.potential x :=
  Iff.rfl

/-- The convention `E_nK(α) = X` for non-big classes is built into the
intersection. -/
theorem nonKahlerLocus_eq_univ_of_not_isBigClass {alpha : RealBottChern n M}
    (h : ¬ IsBigClass alpha) : nonKahlerLocus alpha = univ := by
  apply Set.eq_univ_of_forall
  intro x T
  exact (h ⟨T⟩).elim

/-- The non-nef locus `E_nn(α) = ⋃_{ε > 0} E_nK(α + ε{ω})`. -/
def nonNefLocus (omega : KahlerBackground n M) (alpha : RealBottChern n M) : Set M :=
  ⋃ epsilon : PositiveError,
    nonKahlerLocus
      (alpha + (epsilon : ℝ) • RealBottChern.ofRepresentative omega.form)

@[simp] theorem mem_nonNefLocus {omega : KahlerBackground n M}
    {alpha : RealBottChern n M} {x : M} :
    x ∈ nonNefLocus omega alpha ↔
      ∃ epsilon : PositiveError,
        x ∈ nonKahlerLocus
          (alpha + (epsilon : ℝ) • RealBottChern.ofRepresentative omega.form) := by
  simp only [nonNefLocus, Set.mem_iUnion]

/-- The actual non-nef locus, packaged as the scaffold's locus input. -/
def nonNefLocusData (omega : KahlerBackground n M) : NonNefLocusData n M where
  locus := nonNefLocus omega

/-- A potential is smooth near `p` when it agrees on an open neighbourhood of
`p` with a real function that is smooth in every chart over that
neighbourhood. -/
def IsSmoothNear (u : M → EReal) (p : M) : Prop :=
  ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ h : M → ℝ,
    (∀ e : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U)) ∧
    ∀ y ∈ U, u y = (h y : EReal)

/-- `V` is an irreducible component of `S`: a closed irreducible analytic
subvariety contained in `S` and maximal among such subvarieties. -/
def IsIrreducibleComponent (V : ClosedIrreducibleAnalyticSubvariety n M)
    (S : Set M) : Prop :=
  V.carrier ⊆ S ∧
    ∀ Z : ClosedIrreducibleAnalyticSubvariety n M,
      V.carrier ⊆ Z.carrier → Z.carrier ⊆ S → Z.carrier = V.carrier

/-- The singular locus `V_sing = V \ V_reg`, with `V_reg` the regular points of
the certified dimension. -/
def singularLocus (V : ClosedIrreducibleAnalyticSubvariety n M) : Set M :=
  V.carrier \ regularLocus (n := n) V.carrier V.dim

end

end SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
