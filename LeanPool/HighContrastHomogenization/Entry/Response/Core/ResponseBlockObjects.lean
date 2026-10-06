/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.ReferenceComparison
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedDomainLocality
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Geometry.CanonicalMetricBounds
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.GeometricMean
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ResponseTransferHelpers
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.EccentricityScaleDecay
public import LeanPool.HighContrastHomogenization.Entry.Source.AdaptedBound
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryExponent
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.Profile

/-!
# High-contrast homogenization: Entry.Response.Core.ResponseBlockObjects

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The response-transfer block objects

This file collects the objects used throughout the block-algebra decomposition of the response
transfer `p.response.transfer`, near the canonical imbalance `e.response.canonical.imbalance`. It
fixes the doubled block calculus — the block adjoint, the block congruence, the block square root
and the block spectral bound — together with the block response energy, the block response mean
and the block centred response built from a coarse coefficient block. It also introduces the cell
average and the doubled optimizer field, the canonical mean of a scalar field, the annealed block
of a coefficient, an all-scale Besov-type seminorm, and the predicate that a scalar field is a
response cutoff. Only the notation and definitions the later decomposition is built from appear
here, together with the definitional equation lemmas `respLsqMinus_eq_quadratic`,
`respLsqPlus_eq_quadratic` and `respWPlus_eq` recording what `respLsqMinus`/`respLsqPlus`/
`respWPlus` unfold to.
-/

section
/-!
## Definitions for the response-transfer decomposition of `p.response.transfer`

Every definition here transcribes one object of Steps 3-6 of the printed proof of
`p.response.transfer` near `e.response.canonical.imbalance`.  Nothing here is a proof;
the substantive steps of the decomposition are proved in `CenteredEnergyIdentity` and its supporting
modules.

Fixed notation (Step 2, `p.response.transfer`):

* `respGrid jStar F` is the paper's grid `q`, i.e. `Geometry.explicitRoundedGrid jStar
(explicitCanonicalMetric F)`;
* `respCell jStar F u` is `U_u`;
* `respMean P jStar F u` is `E_u = Ahom_{u,q}`;
* `respKappa P jStar F u` is `kappa_u = d(E_u)`;
* `xi = sqrt(eps) * sigma`;
* `respRatio P jStar F s t` is `r = det E_s / det E_t`.

`-- READING:` marks each place where the printed text leaves a choice and this file fixes one.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale blockSub
  coarseBlock matSqrt normalizedBlock schurSigma schurSigmaStar schurSkew)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The raw global-selection output

`RawOutput` bundles the hypotheses of the global-selection output that the response-transfer
decomposition below is stated over. -/

/-- The raw global-selection output, verbatim. -/
structure RawOutput (d : ℕ) (γ : ℝ) (S : SelectionData) (ε σ Cglob Cprof Csrc : ℝ) (H : ℕ)
    (Bresp : ℝ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ) : Prop where
  prob : IsProbabilityMeasure P
  stat : IsStationaryLaw P
  unit : IsUnitRangeLaw P
  ell : CoarseEllipticityDagger P γ E Ψ K Src
  hB : max (S.B0 ε σ) Bresp ≤ B
  hj : 2 * d ≤ 3 ^ jStar
  hsrc : ⌈Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
      Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ)
  symm : IsSymmetricBlockMat F
  pos : Book.Ch02.BlockPosDef F
  hst : s < t
  ht : t = s + (H : ℤ)
  hs_lo : (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s
  ht_hi : t ≤ (jStar : ℤ) + ⌈(B + Cglob) * Real.logb 3 (2 + aspectRatio E)⌉
  cube : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
    HighContrast.centeredCube d (2 * (jStar : ℤ))
  calib_lo : BlockMatLoewnerLE (blockScale (1 - Real.sqrt ε * σ) F)
    (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
  calib_hi : BlockMatLoewnerLE
    (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
    (blockScale (1 + Real.sqrt ε * σ) F)
  det : (d : ℝ)⁻¹ * detIncrement P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s t < σ
  prof : max
      (max (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s s)
        (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s t))
      (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t t) +
    determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s +
    determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t ≤
    Cprof * σ ^ ((1 - γ) / 8)
  ecc : (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^ ((1 : ℝ) / 2) ≤
    (2 + aspectRatio E) ^ Cglob

/-! ## Step 2 notation (`p.response.transfer`) -/

/-- The selected grid `q` of `p.response.transfer`. -/
@[expose]
def respGrid (jStar : ℕ) (F : BlockMat d) : Mat d :=
  Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)

/-- `U_u` (`p.response.transfer`). -/
@[expose]
def respCell (jStar : ℕ) (F : BlockMat d) (u : ℤ) : Set (Vec d) :=
  HighContrast.adaptedCell (respGrid jStar F) u

/-- `E_u = Ahom_{u,q}` (`p.response.transfer`). -/
@[expose]
def respMean (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (u : ℤ) : BlockMat d :=
  adaptedMean P (respGrid jStar F) u

/-- `kappa_u = d(E_u)` (`p.response.transfer`). -/
@[expose]
def respKappa (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (u : ℤ) : ℝ :=
  canonicalImbalance (respMean P jStar F u)

/-- `r = det E_s / det E_t` (`p.response.transfer`).
-- READING: `det` is the determinant of the flattened `2d x 2d` matrix, as everywhere else in
the development (`blockLogDet`, `one_le_det_adaptedMean`). -/
@[expose]
def respRatio (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s t : ℤ) : ℝ :=
  (toFullBlockMat (respMean P jStar F s)).det / (toFullBlockMat (respMean P jStar F t)).det

/-! ## Step 3, the response coordinates (`p.response.transfer`) -/

/-- `h_t = (K - K^t)/2`, the skew half of the Schur coefficient `K` of `E_t`
(`p.response.transfer`). -/
@[expose]
def respSkew (A : BlockMat d) : Mat d :=
  (1 / 2 : ℝ) • (schurSkew A - matTranspose (schurSkew A))

/-- `r_t = (K + K^t)/2`, the symmetric half of `K` (`p.response.transfer`). -/
@[expose]
def respSym (A : BlockMat d) : Mat d :=
  (1 / 2 : ℝ) • (schurSkew A + matTranspose (schurSkew A))

/-- `b_t = S + (K+K^t) S_*^{-1} (K+K^t)/4 = S + r_t S_*^{-1} r_t`
(`p.response.transfer`).
-- READING: `S_*^{-1}` is the lower-right block of `A` (`schurSigmaStar A = A.lowerRight`
-- inverse). -/
@[expose]
def respBlockB (A : BlockMat d) : Mat d :=
  schurSigma A + respSym A * A.lowerRight * respSym A

/-- `m_t = b_t # S_*`, the geometric mean of `b_t` and `S_*` (`p.response.transfer`). -/
@[expose]
def respM (A : BlockMat d) : Mat d :=
  GeometricMean.geoMean (respBlockB A) (schurSigmaStar A)

/-- The primal load `p = m_t^{-1/2} e` (`p.response.transfer`). -/
@[expose]
def respP (A : BlockMat d) (e : Vec d) : Vec d :=
  matVecMul (matSqrt (respM A)⁻¹) e

/-- The dual load `q = m_t^{1/2} e` (`p.response.transfer`). -/
@[expose]
def respQ (A : BlockMat d) (e : Vec d) : Vec d :=
  matVecMul (matSqrt (respM A)) e

/-! ## Step 3, the pathwise and centred responses (`p.response.transfer`) -/

/-- The pathwise response `J(U, p, q'; b)` of AK.HC (2.9), i.e. CoarseGraining's `ResponseJ`
on the adapted cell (`p.response.transfer`).
-- READING: the admissible class of the printed display is CoarseGraining's
`AHarmonicFunction b U`, and the printed `sup` is `ResponseJ`; this is the identification
already used by `Annealed.responseJ_eq_coarseBlock_adapted`. -/
@[expose]
def respJ (qq : Mat d) (u : ℤ) (p q' : Vec d) (b : CoeffField d) : ℝ :=
  ResponseJ (HighContrast.adaptedCell qq u) p q' b

/-- The block energy `x. A x / 2 - p. q'` with `x = (-p, q')`: the right-hand side of
AK.HC (2.15) (`p.response.transfer`), i.e. the printed
`p.Sp/2 + (q'+Kp).S_*^{-1}(q'+Kp)/2 - p.q'` in flattened coordinates.  This is exactly the
right-hand side of `Annealed.responseJ_eq_coarseBlock_adapted`. -/
@[expose]
def blockResponseEnergy (A : BlockMat d) (p q' : Vec d) : ℝ :=
  (1 / 2 : ℝ) * blockVecDot (-p, q') (blockMatVecMul A (-p, q')) - vecDot p q'

/-- The mean identity AK.HC (2.32): `Y = (I_{2d} + R A) x` (`e.response.energy.and.defect`).
Its two components are the printed gradient and flux means `-p + S_*^{-1}(q'+Kp)` and
`q' - K^t S_*^{-1}(q'+Kp) - Sp` (`p.response.transfer`). -/
@[expose]
def blockResponseMean (A : BlockMat d) (x : BlockVec d) : BlockVec d :=
  x + blockMatVecMul (blockSwap d) (blockMatVecMul A x)

/-- The centred response `Jtilde = E[J] - E[(grad v)_U]. E[(b grad v)_U] / 2`
(`p.response.transfer`) evaluated through the block formulas.
-- READING: the checkout has no annealed optimizer-average object, so the centring is written
with the block means of AK.HC (2.32), which is the only form the printed proof ever uses (the
two means are read off the block at `p.response.transfer`). -/
@[expose]
def blockCenteredResponse (A : BlockMat d) (p q' : Vec d) : ℝ :=
  blockResponseEnergy A p q' -
    (1 / 2 : ℝ) * vecDot (blockResponseMean A (-p, q')).1 (blockResponseMean A (-p, q')).2

/-- Congruence `G^t A G` of doubled blocks (`p.response.transfer`). -/
@[expose]
def blockCongr (G A : BlockMat d) : BlockMat d :=
  ofFullBlockMat ((toFullBlockMat G)ᵀ * toFullBlockMat A * toFullBlockMat G)

/-- `D = diag(Id, -Id)` (`p.response.transfer`). -/
@[expose]
def blockD (d : ℕ) : BlockMat d := ⟨1, 0, 0, -1⟩

/-- The adjoint block: replacing `K` by `-K` is congruence by `D`
(`p.response.transfer`, "For the adjoint, replace K by -K"). -/
@[expose]
def blockAdjoint (A : BlockMat d) : BlockMat d := blockCongr (blockD d) A

/-- `Jtilde^-(e)`, the centred response for `(a; p, q - h_t p)`
(`p.response.transfer`). -/
@[expose]
def respCenteredJMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) : ℝ :=
  blockCenteredResponse (respMean P jStar F t) (respP (respMean P jStar F t) e)
    (respQ (respMean P jStar F t) e -
      matVecMul (respSkew (respMean P jStar F t)) (respP (respMean P jStar F t) e))

/-- `Jtilde^+(e)`, the centred response for `(a^t; p, q + h_t p)`
(`p.response.transfer`). -/
@[expose]
def respCenteredJPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) : ℝ :=
  blockCenteredResponse (blockAdjoint (respMean P jStar F t)) (respP (respMean P jStar F t) e)
    (respQ (respMean P jStar F t) e +
      matVecMul (respSkew (respMean P jStar F t)) (respP (respMean P jStar F t) e))

/-! ## Step 4, the self-dual mean and the recentred data
(`p.response.transfer`) -/

/-- The canonical mean `M(F)`: the geometric mean of `F` and `F# = R F^{-1} R`, the unique
positive solution of the Riccati equation `M(F) F^{-1} M(F) = F#`
(`p.response.transfer`, Riccati). -/
@[expose]
def canonicalMean (A : BlockMat d) : BlockMat d :=
  ofFullBlockMat (GeometricMean.geoMean (toFullBlockMat A)
    (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d)))

/-- The skew Schur coefficient `g` of `M(F)` (`p.response.transfer`). -/
@[expose]
def respg (F : BlockMat d) : Mat d := schurSkew (canonicalMean F)

/-- `G = ((Id, 0), (g, Id))` (`p.response.transfer`). -/
@[expose]
def respG (F : BlockMat d) : BlockMat d := ⟨1, 0, respg F, 1⟩

/-- `M_0 = diag(m, m^{-1})` (`p.response.transfer`).
-- READING: the paper's `m` is the canonical metric `m(F)`: the Schur coefficients of `M(F)`
are `(m, m, g)` by self-duality , and `explicitCanonicalMetric F` is by definition the inverse
of the lower-right block of `M(F)`, i.e. the Schur `sigma_*` of `M(F)`. -/
@[expose]
def respM0 (F : BlockMat d) : BlockMat d :=
  ⟨explicitCanonicalMetric F, 0, 0, (explicitCanonicalMetric F)⁻¹⟩

/-- The positive square root `M^{1/2}` of a doubled block. -/
@[expose]
def blockSqrt (A : BlockMat d) : BlockMat d :=
  ofFullBlockMat (matSqrt (toFullBlockMat A))

/-- `Ehat_u^- = G^t E_u G` (`p.response.transfer`). -/
@[expose]
def respEhatMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (u : ℤ) :
    BlockMat d :=
  blockCongr (respG F) (respMean P jStar F u)

/-- `Ehat_u^+ = D Ehat_u^- D` (`p.response.transfer`). -/
@[expose]
def respEhatPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (u : ℤ) :
    BlockMat d :=
  blockAdjoint (respEhatMinus P jStar F u)

/-- `a_- = a - g` (`p.response.transfer`). -/
@[expose]
def respCoeffMinus (F : BlockMat d) (a : CoeffSpace d) : CoeffField d :=
  fun x => (⇑a.1 : CoeffField d) x - respg F

/-- `a_+ = a^t + g` (`p.response.transfer`). -/
@[expose]
def respCoeffPlus (F : BlockMat d) (a : CoeffSpace d) : CoeffField d :=
  fun x => matTranspose ((⇑a.1 : CoeffField d) x) + respg F

/-- `q^- = q + (g - h_t)p` (`p.response.transfer`). -/
@[expose]
def respqMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    Vec d :=
  respQ (respMean P jStar F t) e +
    matVecMul (respg F - respSkew (respMean P jStar F t)) (respP (respMean P jStar F t) e)

/-- `q^+ = q + (h_t - g)p` (`p.response.transfer`). -/
@[expose]
def respqPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    Vec d :=
  respQ (respMean P jStar F t) e +
    matVecMul (respSkew (respMean P jStar F t) - respg F) (respP (respMean P jStar F t) e)

/-- `x^- = (-p, q^-)` (`p.response.transfer`). -/
@[expose]
def respxMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    BlockVec d :=
  (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)

/-- `x^+ = (-p, q^+)` (`p.response.transfer`). -/
@[expose]
def respxPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    BlockVec d :=
  (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)

/-- `(L^-)^2 = x^-. Ehat_t^- x^-` (`p.response.transfer`). -/
@[expose]
def respLsqMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    ℝ :=
  blockVecDot (respxMinus P jStar F t e)
    (blockMatVecMul (respEhatMinus P jStar F t) (respxMinus P jStar F t e))

/-- `respLsqMinus` is definitionally the quadratic form of `respxMinus` under
`respEhatMinus`. -/
theorem respLsqMinus_eq_quadratic (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) :
    respLsqMinus P jStar F t e
      = blockVecDot (respxMinus P jStar F t e)
          (blockMatVecMul (respEhatMinus P jStar F t) (respxMinus P jStar F t e)) :=
  rfl

/-- `(L^+)^2 = x^+. Ehat_t^+ x^+` (`p.response.transfer`). -/
@[expose]
def respLsqPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    ℝ :=
  blockVecDot (respxPlus P jStar F t e)
    (blockMatVecMul (respEhatPlus P jStar F t) (respxPlus P jStar F t e))

/-- `respLsqPlus` is definitionally the quadratic form of `respxPlus` under
`respEhatPlus`. -/
theorem respLsqPlus_eq_quadratic (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) :
    respLsqPlus P jStar F t e
      = blockVecDot (respxPlus P jStar F t e)
          (blockMatVecMul (respEhatPlus P jStar F t) (respxPlus P jStar F t e)) :=
  rfl

/-- `Y^- = (I_{2d} + R Ehat_t^-) x^-` (`e.response.energy.and.defect`). -/
@[expose]
def respYMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    BlockVec d :=
  blockResponseMean (respEhatMinus P jStar F t) (respxMinus P jStar F t e)

/-- `Y^+ = (I_{2d} + R Ehat_t^+) x^+` (`e.response.energy.and.defect`). -/
@[expose]
def respYPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    BlockVec d :=
  blockResponseMean (respEhatPlus P jStar F t) (respxPlus P jStar F t e)

/-! ## Step 4, the annealed energies and the defect (`p.response.transfer`) -/

/-- `E[J_t^-] = E[J(U_t, p, q^-; a_-)]` (`p.response.transfer`). -/
@[expose]
def respEJMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    ℝ :=
  ∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
    (respCoeffMinus F a) ∂P

/-- `E[J_t^+] = E[J(U_t, p, q^+; a_+)]` (`p.response.transfer`). -/
@[expose]
def respEJPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    ℝ :=
  ∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
    (respCoeffPlus F a) ∂P

/-- `tau^- = E[J(U_s, p, q^-; a_-) - J_t^-]` (`e.response.energy.and.defect`). -/
@[expose]
def respTauMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (e : Vec d) : ℝ :=
  (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
    (respCoeffMinus F a) ∂P) - respEJMinus P jStar F t e

/-- `tau^+ = E[J(U_s, p, q^+; a_+) - J_t^+]` (`e.response.energy.and.defect`). -/
@[expose]
def respTauPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (e : Vec d) : ℝ :=
  (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
    (respCoeffPlus F a) ∂P) - respEJPlus P jStar F t e

/-! ## Step 5, the grid sums and the weak seminorm (`p.response.transfer`) -/

/-- The index set of the scale-`(t-n)` triadic subcells of the cube of generation `t`: the
`w` in `Z^d` with `|w i| <= (3^n-1)/2`.
-- READING: the printed sums run over `z` in `3^k q Z^d` meeting `U_t`, with `k = t - n`; on the
aligned grid these are exactly the `3^{nd}` cells `adaptedCellAtCenter q (t-n) w` of the triadic
partition of `U_t`, indexed by this box. -/
@[expose]
def triadicIndexBox (d : ℕ) (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(((3 ^ n - 1) / 2 : ℕ) : ℤ)) (((3 ^ n - 1) / 2 : ℕ) : ℤ)

/-- The cell average `(X)_V` of a doubled field. -/
@[expose]
def cellAverage (V : Set (Vec d)) (X : Vec d → BlockVec d) : BlockVec d :=
  (fun i => volumeAverage V fun x => (X x).1 i, fun i => volumeAverage V fun x => (X x).2 i)

/-- The doubled optimizer field `X = (grad v, b grad v)` (`e.response.energy.and.defect`). -/
@[expose]
def optimizerField {U : Set (Vec d)} (b : CoeffField d) (u : AHarmonicFunction b U) :
    Vec d → BlockVec d :=
  fun x => (u.toH1.grad x, matVecMul (b x) (u.toH1.grad x))

/-- The concrete scale-average seminorm of AK.HC (2.130) on the selected grid
(`p.response.transfer`):
`sum_{k <= t} 3^{k/2} (avg_{z} |(Z)_{z+U_k}|^2)^{1/2}`, with `k = t - n`.
-- READING: `avg n w` is the cell average `(Z)_{z+U_k}` at the cell indexed by `w` at scale
`k = t - n`; the inner bars are the Euclidean norm of the doubled vector. -/
@[expose]
def besovSeminorm (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d) : ℝ :=
  ∑' n : ℕ, (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
    Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w))

/-- `W = 3^{-t} E[ [M_0^{1/2}(X_t - Y)]^2 ]` (`p.response.transfer`).
-- READING: the checkout exports `IsResponseMaximizer` as a predicate but no existence theorem
producing a maximizer term, so `W` is the supremum of the weak energies over all families of
maximizers of `J(U_t, p, q'; b a)`; the junk value on an empty family is `0`.  Every printed
use of `W` is an upper bound on it, so the supremum is the conservative reading. -/
@[expose]
def respWeakEnergy (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ) (M0 : BlockMat d)
    (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) : ℝ :=
  sSup {c : ℝ |
    ∃ u : (a : CoeffSpace d) → AHarmonicFunction (b a) (HighContrast.adaptedCell qq t),
      (∀ a, IsResponseMaximizer (HighContrast.adaptedCell qq t) p q' (b a) (u a)) ∧
      c = (3 : ℝ) ^ (-(t : ℝ)) *
        ∫ a, besovSeminorm t (fun n z =>
              blockMatVecMul (blockSqrt M0)
                (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z) (optimizerField (b a) (u a)) -
                  Y)) ^ 2 ∂P}

/-- `W^-` (`p.response.transfer`). -/
@[expose]
def respWMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    ℝ :=
  respWeakEnergy P (respGrid jStar F) t (respM0 F) (respP (respMean P jStar F t) e)
    (respqMinus P jStar F t e) (respCoeffMinus F) (respYMinus P jStar F t e)

/-- `W^+` (`p.response.transfer`). -/
@[expose]
def respWPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    ℝ :=
  respWeakEnergy P (respGrid jStar F) t (respM0 F) (respP (respMean P jStar F t) e)
    (respqPlus P jStar F t e) (respCoeffPlus F) (respYPlus P jStar F t e)

/-- `W^+` is the weak energy of the recentred coefficient `a_+ = a^t + g` at the load `q^+`: by
definition `W^+ = W(U_t, p, q^+; a_+, Y^+)` for the weak response energy `W`. -/
theorem respWPlus_eq (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) :
    respWPlus P jStar F t e
      = respWeakEnergy P (respGrid jStar F) t (respM0 F) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F) (respYPlus P jStar F t e) := rfl

/-- The norm of the spectral positive part of a symmetric doubled block: the least `c >= 0`
with `H <= c I_{2d}` (`p.response.transfer`, "the subscript + denotes the spectral
positive part"). -/
@[expose]
def blockSpecBound (Hb : BlockMat d) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ BlockMatLoewnerLE Hb (blockScale c (Book.Ch02.blockIdentity d))}

/-- The all-scale maximum
`M = sup_{k <= t} 3^{-rho(t-k)} max_z |(E_t^{-1/2} A_k(z) E_t^{-1/2} - I_{2d})_+|`
(`p.response.transfer`), pathwise in the sample `a`. -/
@[expose]
def respAllScaleMax (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (a : CoeffSpace d) : ℝ :=
  sSup {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
      blockSpecBound (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}

/-- The **two-sided** all-scale maximum
`A = sup_{k <= t} 3^{-rho(t-k)} |E_t^{-1/2} A_k(z) E_t^{-1/2} - I_{2d}|`, pathwise in the
sample `a`: exactly `respAllScaleMax` with the spectral positive part `blockSpecBound`
replaced by the full operator norm `blockOpNorm` (`HCPoly/Entry/Setup/ProjectiveDistance.lean`).  It
dominates `respAllScaleMax` termwise, since `blockSpecBound N <= blockOpNorm N` always. -/
@[expose]
def respAllScaleAbs (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (a : CoeffSpace d) : ℝ :=
  sSup {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
      blockOpNorm (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}

/-! ## Step 6, the source load and the cutoff class (`p.response.transfer`) -/

/-- The annealed block `E[A(V; b)]` of a field family `b` that need not be a member of the
coefficient carrier (the recentred fields `a_-`, `a_+`); entrywise, as `annealedBlock`. -/
@[expose]
def annealedBlockOf (P : Measure (CoeffSpace d)) (V : Set (Vec d))
    (b : CoeffSpace d → CoeffField d) : BlockMat d :=
  { upperLeft := Matrix.of fun i j => ∫ a, (coarseBlockMatrix V (b a)).upperLeft i j ∂P
    upperRight := Matrix.of fun i j => ∫ a, (coarseBlockMatrix V (b a)).upperRight i j ∂P
    lowerLeft := Matrix.of fun i j => ∫ a, (coarseBlockMatrix V (b a)).lowerLeft i j ∂P
    lowerRight := Matrix.of fun i j => ∫ a, (coarseBlockMatrix V (b a)).lowerRight i j ∂P }

/-- `L_s = sum_{k <= s} 3^{3(k-s)/2} avg_z (|b_{k,z}^{1/2} P| + |(S_{*,k,z})^{-1/2} Q|)^2`
(`p.response.transfer`), with `b_{k,z}` and `(S_{*,k,z})^{-1}` the two diagonal
blocks of `E[A(z+U_k; b)]` and `(P, Q) = Y`.
-- READING: `|b^{1/2}P|^2 = P.bP` and `|(S_*)^{-1/2}Q|^2 = Q.S_*^{-1}Q`, and `S_*^{-1}` is the
lower-right block, as in `schurSigmaStar`. -/
@[expose]
def respSourceLoad (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s : ℤ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) : ℝ :=
  ∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
    ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
              Y.2))) ^ 2)

/-- `L_s^-` (`p.response.transfer`). -/
@[expose]
def respLsMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (e : Vec d) : ℝ :=
  respSourceLoad P jStar F s (respCoeffMinus F) (respYMinus P jStar F t e)

/-- `L_s^+` (`p.response.transfer`). -/
@[expose]
def respLsPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (e : Vec d) : ℝ :=
  respSourceLoad P jStar F s (respCoeffPlus F) (respYPlus P jStar F t e)

/-- The universal profile constant of the smooth cutoff construction:
`max 1 (max θ' θ'')` for the fixed one-dimensional transition profile
`HCPolySupport.smoothTransitionProfile` (`Real.smoothTransition`) used by CoarseGraining's
`QuantitativeCubeCutoff.canonicalFun`.  It is a single real number `≥ 1` depending on NOTHING --
not on `d`, not on `t`, not on the grid -- so every constant built with it below is still a
dimensional constant in the sense of the manuscript.

It is carried explicitly because the pinned package supplies only NONCOMPUTABLE compactness
bounds for the derivatives of `Real.smoothTransition`
(`Sobolev/Foundations/Cutoff/Profile.lean`, both `Classical.choose` of an existence
statement), so no numeral bounds them; and the cutoff constants carry exactly this factor
(`1024 * d ^ 4 * (max 1 (max derivBound secondDerivBound)) ^ 2 * 3 ^ (-2 * t)`). -/
@[expose]
def responseCutoffProfileConst : ℝ :=
  max 1 (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)

/-- `responseCutoffProfileConst` is at least `1`, immediate from its definition as a max with
`1`. -/
theorem one_le_responseCutoffProfileConst : (1 : ℝ) ≤ responseCutoffProfileConst :=
  le_max_left _ _

/-- `responseCutoffProfileConst` is strictly positive, since it is at least `1`. -/
theorem responseCutoffProfileConst_pos : (0 : ℝ) < responseCutoffProfileConst :=
  lt_of_lt_of_le one_pos one_le_responseCutoffProfileConst

/-- The cutoff class of `p.response.transfer`: a cutoff `phi` in `U_t` with
`0 <= phi <= 2`, mean one on `U_t`, and derivatives at the scale `3^t` in `q`-coordinates.
-- READING: "smooth, with derivatives at the scale 3^t in q-coordinates" is rendered as: the
pullback `y -> phi (q y)` is Lipschitz with constant `C(d) * 3^{-t}`, `C(d) = 32 d^2`.  Only this
quantitative form is used in the cutoff estimate.

The Lipschitz constant carries the dimensional factor `3 ^ (-t)`: without it the class is empty,
since every point of a cube of side `3^t` lies at sup-distance at most `3^t/2` from the
complement, so a `3^{-t}`-Lipschitz function vanishing off the cube is at most `1/2` everywhere
and cannot have mean one.  The class is inhabited -- `exists_isResponseCutoff`
 constructs a member.

The coefficient `32 * d ^ 2 * 3 ^ (-t)` is the explicit dimensional constant of the smooth
cutoff construction.  The pullback gradient of the normalized canonical product cutoff is
bounded by `32 * d ^ 2 * smoothTransitionProfile.derivBound * 3 ^ (-t)`
-- reciprocal collar width `16 * d * 3 ^ (-t)`, doubled by the normalization `A⁻¹ ≤ 2`
-- and that is precisely the coefficient used in the cutoff estimates.  Taking the
one-dimensional transition profile piecewise linear, i.e. `derivBound = 1`, turns that
coefficient into the numeral `32 * d ^ 2` used here; the witness built in
`exists_isResponseCutoff` is such a piecewise-linear cutoff and in fact achieves
`8 * d * 3 ^ (-t)`.

The cutoff estimate `abs_cutoffProductTermOnCube_le_scaledWeakNormProduct`
 consumes smoothness and a second-derivative scale, so the class
carries four further conjuncts beyond the first five (the first five keep their names, their
order and their meaning, so every existing projection `hphi.1`, `hphi.2.1`,... is unchanged):

* `ContDiff R (top : N-infty) phi` -- the paper's "SMOOTH cutoff", `p.response.transfer`;
* `HasCompactSupport phi`;
* `tsupport phi subseteq HighContrast.adaptedCell qq t` -- the adapted-geometry form of
  `tsupport phi subseteq openCubeSet Q`, sharpening the pointwise vanishing conjunct to vanishing
  on a neighbourhood of the complement (`HighContrast.adaptedCell qq t` is open);
* the second-derivative bound in `q`-coordinates,
  `forall x, ‖iteratedFDeriv R 2 (phi o q) x‖ <= 1024 * d ^ 4 * Theta ^ 2 * 3 ^ (-2 * t)`,
  the second-order coefficient of the smooth cutoff construction.

The two second-block coefficients are not the flat numerals `32 * d ^ 2` and `1024 * d ^ 4` (their
values at `derivBound = secondDerivBound = 1`): those numerals are not attainable by any smooth
cutoff reachable from the pinned package.  The coefficients carried by the smooth construction are
`32 * d ^ 2 * derivBound * 3 ^ (-t)` and
`1024 * d ^ 4 * (max 1 (max derivBound secondDerivBound)) ^ 2 * 3 ^ (-2 * t)`, whose profile
factors equal `1` only for the piecewise-linear profile, which is not `C^infinity`; and the pinned
package's smooth profile `HCPolySupport.smoothTransitionProfile` carries only the noncomputable
compactness bounds `smoothTransitionProfile.derivBound`/`secondDerivBound`
(`.lake/packages/CoarseGraining/HCPolySupport/Sobolev/Foundations/Cutoff/Profile.lean`,
each `Classical.choose` of a bare existence statement), which no numeral bounds.  Both
coefficients therefore carry the universal factor `Theta = responseCutoffProfileConst >= 1`
above.  Since `Theta >= 1` this only widens
the class, so the estimates that consume membership are strengthened, `exists_isResponseCutoff`
(which produces membership) still discharges the paper's choice, and
`response_cutoff_estimate` is unaffected. -/
@[expose]
def IsResponseCutoff (qq : Mat d) (t : ℤ) (φ : Vec d → ℝ) : Prop :=
  (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 2) ∧
    (∀ x, x ∉ HighContrast.adaptedCell qq t → φ x = 0) ∧
    volumeAverage (HighContrast.adaptedCell qq t) φ = 1 ∧
    LipschitzWith
      (Real.toNNReal
        (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)))
      (fun y : Vec d => φ (matVecMul qq y)) ∧
    ContDiff ℝ (⊤ : ℕ∞) φ ∧
    HasCompactSupport φ ∧
    tsupport φ ⊆ HighContrast.adaptedCell qq t ∧
    ∀ x : Vec d,
      ‖iteratedFDeriv ℝ 2 (fun y : Vec d => φ (matVecMul qq y)) x‖ ≤
        1024 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t)

end

end HCPolySupport.HighContrast.Multiscale
end
