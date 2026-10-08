/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitMaximumEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Window.SuccessorTail
public import LeanPool.HighContrastHomogenization.Provider.Window.Successor

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnSplitSuccessorEnvelope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split maximal envelope over the window's successor scale

The mesoscale envelope the burn split consumes — the truncated standard-cube
bound `3^{g(m-h-k)_+}` whose localizing cube sits `h` scales above the
envelope's own base — is the window's own improved discount: `badScaleEvent`
is its negation at depth `h`, `successorScale` is the strict successor of the
bad scales, and `improved_discount_of_successorScale_le` is the implication.
A coupled window of height `h = 2D` therefore supplies the input of
`henvMax_burnsplit_of_isotropyReference` outright, and the maximal envelope at
the isotropy block holds with the dimension-only constant `4/(1+cIso)` over the
successor scale of that window.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The mesoscale envelope from the window's successor scale.**  Almost
surely, once the successor scale of a window of height `2D` has burned at
scale `m`, every standard cube centered in `□_m` obeys the truncated envelope
`3^{g(m-2D-k)_+}·E`. -/
theorem mesoEnvelope_of_successorScale [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {D : ℕ} (hdepth : M - jStar = ((2 * D : ℕ) : ℤ)) :
    ∀ᵐ a ∂P, ∀ m : ℤ,
      (successorScale g E (M - jStar) a).toReal ≤ (3 : ℝ) ^ m →
      ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * (D : ℝ) - (k : ℝ)) 0)) E) := by
  filter_upwards [Window.ae_successorScale_ne_top hstat hdag hQ hw] with a hfin
  intro m hle k hk w hw'
  have hsucc : successorScale g E (M - jStar) a ≤
      ENNReal.ofReal ((3 : ℝ) ^ m) := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hle
  have hbase :=
    Window.improved_discount_of_successorScale_le hdag hsucc k hk w hw'
  have hcast : ((M : ℝ) - (jStar : ℝ)) = 2 * (D : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hdepth
    push_cast at h
    linarith only [h]
  rwa [hcast] at hbase

/-- **The maximal envelope at the isotropy block over the window's successor
scale.**  The burn-split chain with its mesoscale input discharged: the
normalizing constant is `4/(1+cIso)`, with no reference ratio and no boundary
constant. -/
theorem henvMax_burnsplit_of_successorScale [NeZero d]
    (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {D : ℕ} (hdepth : M - jStar = ((2 * D : ℕ) : ℤ))
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    (hD : boundaryConst Cd g nu ≤ (3 : ℝ) ^ D)
    {rho : ℝ} (hrho : g ≤ rho) (t : ℤ)
    (hgeom : ∀ k : ℤ, k ≤ t →
      ∀ w ∈ Response.alignedIndex (roundedGrid l nu) k t,
        adaptedCellAt (roundedGrid l nu) k w ⊆
          centeredCube d (t + (D : ℤ)))
    {cIso : ℝ} (hcIso : 0 ≤ cIso) :
    ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l nu) t
          (isotropyReference cIso E) a ≤
        ENNReal.ofReal
          (4 / (1 + cIso) *
            ((max 1
              (3 * (successorScale g E (M - jStar) a).toReal *
                (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))))) ^ g / 2)) :=
  henvMax_burnsplit_of_isotropyReference hd hg hdag.refBlock_isSymm
    hdag.refBlock_posDef
    (mesoEnvelope_of_successorScale hstat hdag hQ hw hdepth)
    hl hCd hnu hD hrho t hgeom hcIso

end

end HCPolySupport.HighContrast.Quenched
