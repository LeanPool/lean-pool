/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Moments

/-!
# High-contrast homogenization: Setup.SourceObjects

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Source-window and source-control carriers

The objects of the source-control subsection and of the random-source window:
the geometric series `ζ_g`, `χ_g`, the witness eccentricity `𝔢_q` and the
boundary constant `B_q`, the cross-grid factor `K(q,q')`, the dual reference
block `𝐄_*` and the reference ratio `κ_𝐄`, the source growth witness `K̄_S`,
the weak-Orlicz moment multiplier `𝔐_p`, the source burn `j_S`, the coupled
window pair, the source-remainder scale `a_{j_*}^S`, the fixed-history
exponents, and the window multiplier `Y_P` presented as data together with the
properties the window lemma establishes for it.

`Λ(F;𝐄) = |F^{-1/2}𝐄F^{-1/2}|` is `blockSize 𝐄 F`, and
`|𝐄^{-1/2}𝐀(V)𝐄^{-1/2}|` is `blockSize (coarseBlock V a) 𝐄`; the single
carrier `blockSize` serves both, and the sharp-adjoint normalization
`|𝐄_*^{1/2}𝐀_*^{-1}(V)𝐄_*^{1/2}|` is `blockSize (coarseStarInv V a)`
`(blockReflect 𝐄)`, the dual reference block being `𝐄_*^{-1} = R 𝐄 R`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped ENNReal

open scoped Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-! ## The sharp-adjoint response -/

/-- The inverse sharp-adjoint coarse response `𝐀_*^{-1}(U; a)`
(the dual of the coarse block). -/
@[expose]
def coarseStarInv (U : Set (Vec d)) (a : CoeffSpace d) : BlockMat d :=
  coarseStarredBlockMatrixInv U ⇑a.1

/-! ## The geometric series and the grid constants -/

/-- `ζ_g = Σ_{u ≥ 0} 3^{-(1-g)u} = (1 - 3^{-(1-g)})^{-1}`, for `0 ≤ g < 1`. -/
@[expose]
def zetaG (g : ℝ) : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 - g)))⁻¹

/-- `χ_g = Σ_{u ≥ 1} 3^{-(1-g)u} = (3^{1-g} - 1)^{-1}`, for `0 ≤ g < 1`. -/
@[expose]
def chiG (g : ℝ) : ℝ :=
  ((3 : ℝ) ^ (1 - g) - 1)⁻¹

/-- The witness eccentricity `𝔢_q = (|m| |m^{-1}|)^{1/2}` of a rounded grid
presented with its positive witness `m`; a function of the witness alone. -/
@[expose]
def witnessEccentricity (m : Mat d) : ℝ :=
  Real.sqrt (specBound m * specBound m⁻¹)

/-- The boundary constant `B_q = C_d 𝔢_q ζ_g`, with the dimensional constant of
the source-control subsection carried explicitly. -/
@[expose]
def boundaryConst (Cd g : ℝ) (m : Mat d) : ℝ :=
  Cd * witnessEccentricity m * zetaG g

/-- The cross-grid factor `K(q,q') = (1 + |q^{-1}q'| + |(q')^{-1}q|)^{2d}`. -/
@[expose]
def gridRatio (q q' : Mat d) : ℝ :=
  (1 + ‖q⁻¹ * q'‖ + ‖(q')⁻¹ * q‖) ^ (2 * d)

/-- The reference ratio `κ_𝐄 = |𝐄_*^{-1/2}𝐄𝐄_*^{-1/2}|`. -/
@[expose]
def kappaRef (E : BlockMat d) : ℝ :=
  blockSize E (blockSharp E)

/-! ## The source gauge, the burn, and the window -/

/-- `K̄_S = max{2, K_{Ψ_S}}`. -/
@[expose]
def growthBar (K : ℝ) : ℝ :=
  max 2 K

/-- The weak-Orlicz moment multiplier
`𝔐_p(K̄) = (1 + 2p K̄^{⌈p(p+1)/2⌉}(1 + log K̄))^{1/p}`
(the moment bound for the source scale furnished by its tail gauge). -/
@[expose]
def momentMultiplier (p Kbar : ℝ) : ℝ :=
  (1 + 2 * p * Kbar ^ (⌈p * (p + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar)) ^ p⁻¹

/-- The source burn `j_S` (`e.source.lower.scale`). -/
@[expose]
def sourceBurn (d : ℕ) (Q K : ℝ) : ℤ :=
  max (kZero d : ℤ)
    (max ⌈2 * Real.logb 3 (growthBar K)⌉
      ⌈2 + 4 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K) +
        Real.logb 3 (momentMultiplier Q (growthBar K))⌉)

/-- A coupled window pair `(j_*, M)`
(the containing window on which the single source multiplier is built). -/
@[expose]
def IsCoupledWindow (d : ℕ) (Q K : ℝ) (jStar M : ℤ) : Prop :=
  sourceBurn d Q K ≤ jStar ∧ jStar + 1 ≤ M ∧
    (d : ℝ) * ((M : ℝ) - (jStar : ℝ)) +
        16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K) ≤
      (4 * (d : ℝ) + 3) * (jStar : ℝ)

/-- The source-remainder scale `a_{j_*}^S = K̄_S^{4(d+1)}3^{2-j_*}`
(the residual source parameter at the lower generation). -/
@[expose]
def sourceRemainderScale (d : ℕ) (jStar : ℤ) (K : ℝ) : ℝ :=
  growthBar K ^ (4 * (d + 1)) * (3 : ℝ) ^ (2 - jStar)

/-- The positive-part discount `3^{g(j_* - a)_+}` carried by every cell bound
of the window (`e.source.adapted.bound`). -/
@[expose]
def burnDiscount (g : ℝ) (jStar a : ℤ) : ℝ :=
  (3 : ℝ) ^ (g * max ((jStar : ℝ) - (a : ℝ)) 0)

/-! ## The fixed-history exponents -/

/-- `Q = 2⌈2(d+1)/(1-g)⌉`
(`e.scale.selection.Q.choice`). -/
@[expose]
def initExpQ (d : ℕ) (g : ℝ) : ℕ :=
  2 * ⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊

/-- `a = (1-g)/4` (`e.scale.selection.Q.choice`). -/
@[expose]
def initExpA (g : ℝ) : ℝ :=
  (1 - g) / 4

/-- `ρ_max = g + (d + a)/Q` (`e.scale.selection.Q.choice`). -/
@[expose]
def initExpRhoMax (d : ℕ) (g : ℝ) : ℝ :=
  g + ((d : ℝ) + initExpA g) / (initExpQ d g : ℝ)

/-- `ρ_dr = a/2` (`e.scale.selection.Q.choice`). -/
@[expose]
def initExpRhoDr (g : ℝ) : ℝ :=
  initExpA g / 2

/-! ## The window multiplier as data -/

/-- The common source multiplier of a bounded window, presented as data with
exactly the properties `e.source.multiplier` establishes for it: it is at
least one, it dominates the coarse response and its sharp adjoint on every
standard aligned cube and on every adapted cell of every deterministic rounded
grid at alignment `j_*` inside the window, simultaneously and on one event of
full measure, and its excess over one has the source gauge's weak-Orlicz tail
at the remainder scale, with the resulting `L^p` moment bound.

The window, the grids, the scales and the cells are deterministic and fixed
before the multiplier is read; that is the quantifier order below, in which the
cell families are bound outside the almost-everywhere quantifier. -/
structure IsWindowMultiplier (P : Measure (CoeffSpace d)) (g : ℝ) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (K Cd : ℝ) (jStar M : ℤ) (Y : CoeffSpace d → ℝ) : Prop where
  measurable : Measurable Y
  one_le : ∀ a, 1 ≤ Y a
  standard_primal : ∀ᵐ a ∂P, ∀ (k : ℤ) (w : Fin d → ℤ),
    standardCell d k w ⊆ centeredCube d M →
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (blockScale (Y a * burnDiscount g jStar k) E)
  standard_adjoint : ∀ᵐ a ∂P, ∀ (k : ℤ) (w : Fin d → ℤ),
    standardCell d k w ⊆ centeredCube d M →
    BlockMatLoewnerLE (coarseStarInv (standardCell d k w) a)
      (blockScale (Y a * burnDiscount g jStar k) (blockReflect E))
  adapted_primal : ∀ᵐ a ∂P, ∀ (n : Mat d), n.PosDef → ∀ (r : ℤ) (y : Vec d),
    adaptedCellTranslate (roundedGrid jStar n) r y ⊆ centeredCube d M →
      BlockMatLoewnerLE
        (coarseBlock (adaptedCellTranslate (roundedGrid jStar n) r y) a)
        (blockScale (boundaryConst Cd g n * Y a * burnDiscount g jStar r) E)
  adapted_adjoint : ∀ᵐ a ∂P, ∀ (n : Mat d), n.PosDef → ∀ (r : ℤ) (y : Vec d),
    adaptedCellTranslate (roundedGrid jStar n) r y ⊆ centeredCube d M →
      BlockMatLoewnerLE
        (coarseStarInv (adaptedCellTranslate (roundedGrid jStar n) r y) a)
        (blockScale (boundaryConst Cd g n * Y a * burnDiscount g jStar r)
          (blockReflect E))
  orlicz : IndependentSums.IsBigOWith P Ψ (fun a => Y a - 1)
    (sourceRemainderScale d jStar K)
  lp_moment : ∀ p : ℝ, 1 ≤ p →
    eLpNorm Y (ENNReal.ofReal p) P ≤
      ENNReal.ofReal
        (1 + sourceRemainderScale d jStar K * momentMultiplier p (growthBar K))

end

end HighContrast
end HCPolySupport

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-! ## The mixed source-tail relation -/

/-- The mixed source-tail relation `X ≤ b + O_{Ψ_S}(c)` of 02: almost surely
`X ≤ b + Z` for a nonnegative `Z` with the weak-Orlicz tail at scale `c`. -/
@[expose]
def IsShiftedBigOWith (P : Measure (CoeffSpace d)) (Ψ : ℝ → ℝ)
    (X : CoeffSpace d → ℝ) (b c : ℝ) : Prop :=
  ∃ Z : CoeffSpace d → ℝ, (∀ a, 0 ≤ Z a) ∧ (∀ᵐ a ∂P, X a ≤ b + Z a) ∧
    IndependentSums.IsBigOWith P Ψ Z c

/-- The mixed source-tail relation for an extended-real-valued quantity, such
as a supremum over an infinite cell family. -/
@[expose]
def IsShiftedBigOWithTop (P : Measure (CoeffSpace d)) (Ψ : ℝ → ℝ)
    (X : CoeffSpace d → ℝ≥0∞) (b c : ℝ) : Prop :=
  ∃ Z : CoeffSpace d → ℝ, (∀ a, 0 ≤ Z a) ∧
    (∀ᵐ a ∂P, X a ≤ ENNReal.ofReal (b + Z a)) ∧
    IndependentSums.IsBigOWith P Ψ Z c

/-! ## The below-start and cell-family suprema -/

/-- The below-start quantity `S_{t,<j_*}(F)`
(the below-start source maximum): the weighted supremum,
over the scales below the burn and the given below-start centers, of the size
of the positive part of the `F`-normalized excess of the adapted response. -/
@[expose]
def belowStartSup (rho : ℝ) (q : Mat d) (jStar t : ℤ) (Z : ℤ → Set (Vec d))
    (F : BlockMat d) (a : CoeffSpace d) : ℝ≥0∞ :=
  ⨆ (k : ℤ) (_ : k < jStar) (z : Vec d) (_ : z ∈ Z k),
    ENNReal.ofReal
      ((3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
        blockExcess (coarseBlock (adaptedCellTranslate q k z) a) F)

/-- The centered cell-family supremum
`sup_{W ∈ 𝒲} |F^{-1/2}(𝐀(W) - E[𝐀(W)])F^{-1/2}|_{S_Q}`. -/
@[expose]
def cellFamilyCenteredSup (P : Measure (CoeffSpace d)) (Q : ℝ)
    (W : Set (Set (Vec d))) (F : BlockMat d) (a : CoeffSpace d) : ℝ≥0∞ :=
  ⨆ V ∈ W,
    ENNReal.ofReal
      (schattenSize Q (blockSub (coarseBlock V a) (annealedBlock P V)) F)

/-- The mean cell-family supremum `sup_{W ∈ 𝒲} |F^{-1/2}E[𝐀(W)]F^{-1/2}|`. -/
@[expose]
def cellFamilyMeanSup (P : Measure (CoeffSpace d)) (W : Set (Set (Vec d)))
    (F : BlockMat d) : ℝ≥0∞ :=
  ⨆ V ∈ W, ENNReal.ofReal (blockSize (annealedBlock P V) F)

/-- The annealed sharp-adjoint block `E[𝐀_*^{-1}(U;·)]`.  The sharp adjoint is
the block reflection of the response, and the reflection permutes entries, so
the expectation of the reflection is the reflection of the expectation. -/
@[expose]
def annealedStarInv (P : Measure (CoeffSpace d)) (U : Set (Vec d)) : BlockMat d :=
  blockReflect (annealedBlock P U)

/-- The sharp-adjoint centered cell-family supremum. -/
@[expose]
def cellFamilyCenteredSupAdjoint (P : Measure (CoeffSpace d)) (Q : ℝ)
    (W : Set (Set (Vec d))) (F : BlockMat d) (a : CoeffSpace d) : ℝ≥0∞ :=
  ⨆ V ∈ W,
    ENNReal.ofReal
      (schattenSize Q (blockSub (coarseStarInv V a) (annealedStarInv P V)) F)

/-- The sharp-adjoint mean cell-family supremum. -/
@[expose]
def cellFamilyMeanSupAdjoint (P : Measure (CoeffSpace d)) (W : Set (Set (Vec d)))
    (F : BlockMat d) : ℝ≥0∞ :=
  ⨆ V ∈ W, ENNReal.ofReal (blockSize (annealedStarInv P V) F)

end

end HighContrast
end HCPolySupport

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- An admissible index for the grid `q` inside the window `□_M`: the scale is
at or above the burn, the aligned cell at that scale and index is contained in
the window, and so is the centered cell at that scale. -/
@[expose]
def IsAdmissibleIndex (q : Mat d) (jStar M r : ℤ) (w : Fin d → ℤ) : Prop :=
  jStar ≤ r ∧ adaptedCellAt q r w ⊆ centeredCube d M ∧
    adaptedCell q r ⊆ centeredCube d M

end

end HighContrast
end HCPolySupport

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The source constant of the window grid, `K_q^S = κ_𝐄 B_q² 𝒰²`
with `𝒰 = 2`. -/
@[expose]
def initGridConst (Cd g : ℝ) (E : BlockMat d) (mu : Mat d) : ℝ :=
  kappaRef E * boundaryConst Cd g mu ^ 2 * 4

/-- The same constant on the identity grid, `K_I^S = κ_𝐄 𝒰² = 4κ_𝐄`. -/
@[expose]
def initIdentityConst (E : BlockMat d) : ℝ :=
  4 * kappaRef E

end

end HighContrast
end HCPolySupport

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The bad scales of a window and their strict successor -/

/-- The bad-scale event `𝖡_{P,h}(m)` of a window of height `h`: at generation
`m` some standard aligned cube centered in `□_m` exceeds the reference block,
after the discount `3^{-g(m-h-k)_+}` at its own scale `k`. -/
@[expose]
def badScaleEvent (g : ℝ) (E : BlockMat d) (h m : ℤ) (a : CoeffSpace d) : Prop :=
  1 < ⨆ (k : ℤ) (_ : k ≤ m) (w : Fin d → ℤ)
        (_ : standardCellCenter k w ∈ centeredCube d m),
      ENNReal.ofReal
        ((3 : ℝ) ^ (-g * max ((m : ℝ) - (h : ℝ) - (k : ℝ)) 0) *
          blockSize (coarseBlock (standardCell d k w) a) E)

/-- The strict successor of the last bad triadic scale,
`Ŝ_{P,h} = 3 sup({3^m : 𝖡_{P,h}(m) occurs} ∪ {0})`.
The empty supremum is zero, and the value is infinite exactly when the bad
scales are unbounded above. -/
@[expose]
def successorScale (g : ℝ) (E : BlockMat d) (h : ℤ) (a : CoeffSpace d) : ℝ≥0∞ :=
  3 * ⨆ (m : ℤ) (_ : badScaleEvent g E h m a), ENNReal.ofReal ((3 : ℝ) ^ m)

/-- The powered source gauge `Ψ_S^{(g)}(t) = Ψ_S(t^{1/g})`. -/
@[expose]
def poweredGauge (Ψ : ℝ → ℝ) (g : ℝ) : ℝ → ℝ :=
  fun t => Ψ (t ^ g⁻¹)

/-- The powered source-remainder scale
`ã_{j_*,g}^S = K̄_S^{4g(d+1)}3^{g(2-j_*)}`. -/
@[expose]
def poweredRemainderScale (d : ℕ) (jStar : ℤ) (g K : ℝ) : ℝ :=
  growthBar K ^ (4 * g * ((d : ℝ) + 1)) * (3 : ℝ) ^ (g * (2 - (jStar : ℝ)))

end

end HighContrast
end HCPolySupport
