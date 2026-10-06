/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# High-contrast homogenization: Setup.Moments

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Moment and history carriers for the fixed-grid estimates

The objects the fixed-grid section builds on a doubled block matrix and on the
adapted geometry: the Schatten norm `|H|_{S_Q}` and the mixed norm
`‖H‖_{L^Q(S_Q)}`, the scalar sizes `|F^{-1/2}HF^{-1/2}|` and
`|(F^{-1/2}(H-F)F^{-1/2})_+|`, the gain functions `Φ_Q` and `𝔥_Q`, the adapted
moment carriers `A_j^q(z)`, `E_j^q`, `v_j^q`, `Δ_{j,T}^q`, `P_{j,T}^q`, the
portable histories `𝓗_q^cen`, `𝓗_q^nl`, `𝓗_q` and the profile `𝒫_q(T;b)`, the
synchronized charge, and the linear drift.

Three encoding conventions are used throughout and are recorded here.

*Scalar sizes are Loewner.*  For a symmetric `H` and a positive `F` the number
`|F^{-1/2}HF^{-1/2}|` is the least `t ≥ 0` with `-tF ≤ H ≤ tF`, and the size of
the positive part of `F^{-1/2}(H-F)F^{-1/2}` is the least `t ≥ 0` with
`H ≤ (1+t)F`.  Both are written in that form, as the intrinsic contrast and the
scalar bound of the setup layer are; no matrix square root enters a scalar
size.  The reference text never defines the matrix positive part; the Loewner
form is the reading forced by its two uses, that the positive part of a
symmetric matrix is its spectral positive part.

*Schatten sizes are spectral.*  The Schatten norm has no Loewner form, so
`|H|_{S_Q} = (tr((H²)^{Q/2}))^{1/Q}` is written with the continuous functional
calculus of the nonnegative symmetric matrix `H²`, at an arbitrary real
`Q ≥ 1`, and the normalization `F^{-1/2}HF^{-1/2}` is the literal conjugation by
the positive semidefinite square root of `F⁻¹` that the setup layer has already
characterized as the unique such root.

*Failing closed.*  Every quantity whose finiteness is a hypothesis or a
conclusion of the reference text — the mixed norms, the histories, the
profiles, the suprema over infinite cell families — is valued in `ℝ≥0∞`.  An
unbounded supremum or a divergent moment is then `∞` rather than a real junk
value, and the reference text's convention that the supremum of an empty family
of nonnegative quantities is zero is the lattice's own.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-! ## Doubled block arithmetic -/

/-- The difference of two doubled block matrices. -/
@[expose]
def blockSub (A B : BlockMat d) : BlockMat d :=
  { upperLeft := A.upperLeft - B.upperLeft
    upperRight := A.upperRight - B.upperRight
    lowerLeft := A.lowerLeft - B.lowerLeft
    lowerRight := A.lowerRight - B.lowerRight }

/-- The sharp involution `H^♯ = R H^{-1} R` of a positive block, the
conjugation by the reflection being the block reflection of the ambient layer.
At the reference block this is `𝐄_* = (R𝐄R)^{-1}`, and `𝐄_*^{-1} = R𝐄R` is
`blockReflect 𝐄` (the dual of the coarse block). -/
@[expose]
def blockSharp (H : BlockMat d) : BlockMat d :=
  blockReflect (Book.Ch02.blockMatInv H)

/-- The log-determinant of a doubled block matrix. -/
@[expose]
def blockLogDet (H : BlockMat d) : ℝ :=
  Real.log (toFullBlockMat H).det

/-- The trace of a doubled block matrix. -/
@[expose]
def blockTrace (H : BlockMat d) : ℝ :=
  Matrix.trace (toFullBlockMat H)

/-- The normalized block `F^{-1/2} H F^{-1/2}`, the square root being the
positive semidefinite square root of `F⁻¹`. -/
@[expose]
def normalizedBlock (H F : BlockMat d) : BlockMat d :=
  ofFullBlockMat
    (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat H *
      matSqrt ((toFullBlockMat F)⁻¹))

/-! ## Scalar sizes: the Loewner encodings of `|F^{-1/2} · F^{-1/2}|` -/

/-- `|F^{-1/2} H F^{-1/2}|` for a symmetric `H` and a positive `F`: the least
`t ≥ 0` with `-tF ≤ H ≤ tF`.  On a positive `H` the lower constraint is
vacuous.  At `H = 𝐄` this is the normalization `Λ(F;𝐄)` of the source-control
subsection; at `F = 𝐄_*` and `H = 𝐄` it is `κ_𝐄`. -/
@[expose]
def blockSize (H F : BlockMat d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE H (blockScale t F) ∧
    BlockMatLoewnerLE (blockScale (-t) F) H}

/-- `|(F^{-1/2}(H - F)F^{-1/2})_+|`, the size of the positive part of the
`F`-normalized excess: the least `t ≥ 0` with `H ≤ (1+t)F`. -/
@[expose]
def blockExcess (H F : BlockMat d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE H (blockScale (1 + t) F)}

/-! ## The Schatten norm and the mixed norm -/

/-- The Schatten norm `|H|_{S_Q} = (tr((H²)^{Q/2}))^{1/Q}` of a symmetric
doubled block matrix, the power of the nonnegative symmetric matrix `H²` being
taken by the continuous functional calculus. -/
@[expose]
def schattenNorm (Q : ℝ) (H : BlockMat d) : ℝ :=
  (Matrix.trace
      (cfc (fun x : ℝ => x ^ (Q / 2))
        (toFullBlockMat H * toFullBlockMat H))) ^ Q⁻¹

/-- The Schatten norm `|F^{-1/2} H F^{-1/2}|_{S_Q}` of the `F`-normalized
matrix. -/
@[expose]
def schattenSize (Q : ℝ) (H F : BlockMat d) : ℝ :=
  schattenNorm Q (normalizedBlock H F)

/-- The mixed norm `‖F^{-1/2} H F^{-1/2}‖_{L^Q(S_Q)} = (E[|·|_{S_Q}^Q])^{1/Q}`
of a random doubled block matrix normalized by a deterministic positive `F`. -/
@[expose]
def lqSchattenSize (P : Measure (CoeffSpace d)) (Q : ℝ)
    (A : CoeffSpace d → BlockMat d) (F : BlockMat d) : ℝ≥0∞ :=
  eLpNorm (fun a => schattenSize Q (A a) F) (ENNReal.ofReal Q) P

/-- The `L^Q` norm of a real random variable. -/
@[expose]
def lqNorm (P : Measure (CoeffSpace d)) (Q : ℝ) (X : CoeffSpace d → ℝ) : ℝ≥0∞ :=
  eLpNorm X (ENNReal.ofReal Q) P

/-! ## The gain functions -/

/-- `Φ_Q(x) = e^{(1-1/Q)x}(e^x-1)^{1/Q} + (e^x-1)`, for `x ≥ 0`. -/
@[expose]
def gainPhi (Q x : ℝ) : ℝ :=
  Real.exp ((1 - Q⁻¹) * x) * (Real.exp x - 1) ^ Q⁻¹ + (Real.exp x - 1)

/-- `𝔥_Q(P) = (1 + tr(P - I))^Q - 1`, for `P ≥ I`. -/
@[expose]
def frakH (Q : ℝ) (Pm : BlockMat d) : ℝ :=
  (1 + (blockTrace Pm - 2 * (d : ℝ))) ^ Q - 1

/-! ## The adapted moment carriers -/

/-- The center `3^r q w` of the aligned adapted cell `z + ⋄_r^q`,
`z ∈ 3^r 𝕃_q` (the adapted cubes of a rounded geometry). -/
@[expose]
def adaptedCellCenter (q : Mat d) (r : ℤ) (w : Fin d → ℤ) : Vec d :=
  (3 : ℝ) ^ r • matVecMul q (fun i => (w i : ℝ))

/-- The adapted response `A_r^q(z) = 𝐀(z + ⋄_r^q)` at the aligned center
`z = 3^r q w`. -/
@[expose]
def adaptedResponse (q : Mat d) (r : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) :
    BlockMat d :=
  coarseBlock (adaptedCellAt q r w) a

/-- The adapted mean `E_r^q = E[A_r^q(0)]`. -/
@[expose]
def adaptedMean (P : Measure (CoeffSpace d)) (q : Mat d) (r : ℤ) : BlockMat d :=
  annealedBlock P (adaptedCell q r)

/-- Finiteness of the adapted mean: the coarse response over the adapted cell
is integrable, so `E_r^q` is the expectation it names. -/
@[expose]
def HasFiniteAdaptedMean (P : Measure (CoeffSpace d)) (q : Mat d) (r : ℤ) :
    Prop :=
  HasIntegrableCoarseBlock P (adaptedCell q r)

/-- The centered normalized moment
`v_r^q = ‖(E_r^q)^{-1/2}(A_r^q(0) - E_r^q)(E_r^q)^{-1/2}‖_{L^Q(S_Q)}`. -/
@[expose]
def centeredMoment (P : Measure (CoeffSpace d)) (Q : ℝ) (q : Mat d) (r : ℤ) :
    ℝ≥0∞ :=
  lqSchattenSize P Q
    (fun a => blockSub (coarseBlock (adaptedCell q r) a) (adaptedMean P q r))
    (adaptedMean P q r)

/-- The determinant increment
`Δ_{j,T}^q = log det E_j^q - log det E_T^q`. -/
@[expose]
def detIncrement (P : Measure (CoeffSpace d)) (q : Mat d) (j T : ℤ) : ℝ :=
  blockLogDet (adaptedMean P q j) - blockLogDet (adaptedMean P q T)

/-- The relative mean `P_{j,T}^q = (E_T^q)^{-1/2}E_j^q(E_T^q)^{-1/2}`. -/
@[expose]
def relMean (P : Measure (CoeffSpace d)) (q : Mat d) (j T : ℤ) : BlockMat d :=
  normalizedBlock (adaptedMean P q j) (adaptedMean P q T)

/-- The synchronized charge `Δ̂_h^q(T) = Σ_{j=T+1}^{T+h} Δ_{j-h,j}^q`. -/
@[expose]
def synchCharge (P : Measure (CoeffSpace d)) (q : Mat d) (h T : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc (T + 1) (T + h), detIncrement P q (j - h) j

/-! ## The portable histories and the profile -/

/-- The centered history `𝓗_q^cen(b)` (`e.scale.selection.fluctuation.history`). -/
@[expose]
def centeredHistory (P : Measure (CoeffSpace d)) (Q rhoMax : ℝ) (q : Mat d)
    (jStar b : ℤ) : ℝ≥0∞ :=
  ∫⁻ a,
      (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
        ENNReal.ofReal
          ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w a) (adaptedMean P q j))
              (adaptedMean P q b))) ^ Q ∂P

/-- The nonlinear history `𝓗_q^nl(b)` (02, after
`e.scale.selection.fluctuation.history`). -/
@[expose]
def nonlinearHistory (P : Measure (CoeffSpace d)) (Q a : ℝ) (q : Mat d)
    (jStar b : ℤ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Ico jStar b,
    ENNReal.ofReal
      ((3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j b))

/-- The complete history `𝓗_q(b) = 𝓗_q^cen(b) + 𝓗_q^nl(b)`. -/
@[expose]
def portableHistory (P : Measure (CoeffSpace d)) (Q a rhoMax : ℝ) (q : Mat d)
    (jStar b : ℤ) : ℝ≥0∞ :=
  centeredHistory P Q rhoMax q jStar b + nonlinearHistory P Q a q jStar b

/-- The portable profile `𝒫_q(T;b)` (`e.scale.selection.complete.profile`). -/
@[expose]
def portableProfile (P : Measure (CoeffSpace d)) (Q a rhoMax : ℝ) (q : Mat d)
    (jStar b T : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal
      ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b T))) *
      portableHistory P Q a rhoMax q jStar b +
    (∑ j ∈ Finset.Icc (b + 1) T,
      ENNReal.ofReal
          ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j T)) *
        centeredMoment P Q q j ^ Q) +
    ∑ j ∈ Finset.Ico b T,
      ENNReal.ofReal
        ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T))

/-- The linear drift `𝒟_{q,b}^{ρ_dr}(T)`, the determinant drift
`e.scale.selection.determinant.drift` at a general drift exponent. -/
@[expose]
def linearDrift (P : Measure (CoeffSpace d)) (rhoDr : ℝ) (q : Mat d)
    (b T : ℤ) : ℝ :=
  ∑ r ∈ Finset.Icc (b + 1) T,
    (3 : ℝ) ^ (-rhoDr * ((T : ℝ) - (r : ℝ))) *
      blockTrace
        (ofFullBlockMat
          ((toFullBlockMat (adaptedMean P q T))⁻¹ *
            toFullBlockMat
              (blockSub (adaptedMean P q (r - 1)) (adaptedMean P q r))))

/-! ## The contraction parameters -/

/-- The centered contraction factor
`λ_cen = 3^{-ha} + 2^{Q-1}C_rec^Q 3^{-hQd/2}`
(02, in `p.fixed.geometry.one.grid.propagation`). -/
@[expose]
def lambdaCen (d : ℕ) (Q a Crec : ℝ) (h : ℤ) : ℝ :=
  (3 : ℝ) ^ (-(h : ℝ) * a) +
    2 ^ (Q - 1) * Crec ^ Q * (3 : ℝ) ^ (-(h : ℝ) * Q * (d : ℝ) / 2)

/-- The portable contraction factor
`λ_port = max{3^{-ha} + 2^{Q-1}C_rec^Q3^{-hQd/2}, 3^{-ha}}`
(02, in `p.fixed.geometry.one.grid.propagation`). -/
@[expose]
def lambdaPort (d : ℕ) (Q a Crec : ℝ) (h : ℤ) : ℝ :=
  max (lambdaCen d Q a Crec h) ((3 : ℝ) ^ (-(h : ℝ) * a))

end

end HighContrast
end HCPolySupport

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- An aligned adapted cell is the translate of the centered adapted cell by its
own center. -/
theorem adaptedCellAt_eq_adaptedCellTranslate (q : Mat d) (r : ℤ) (w : Fin d → ℤ) :
    adaptedCellAt q r w = adaptedCellTranslate q r (adaptedCellCenter q r w) :=
  rfl

end

end HighContrast
end HCPolySupport
