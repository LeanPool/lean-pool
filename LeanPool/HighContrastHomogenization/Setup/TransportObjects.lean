/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.SourceObjects
public import LeanPool.HighContrastHomogenization.Geometry.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Geometry.Canonical
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge

/-!
# High-contrast homogenization: Setup.TransportObjects

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Carriers for the transport across a change of adapted geometry

The objects the geometry-and-transport section adds to the fixed-grid layer:
the canonical block geometry `A # B`, `M(E)`, `m(E)`, `𝔡(E)`; the determinant
account `Ξ(E)`, `Ξ_j^q`, `σ_q(u,v)`; the gap function `𝔤_Q`; the matrix
positive part; the bridge congruence `S` and its Gram matrix `SᵗS`; the
transport and bridge source coefficients and their remainders; the
constant-speed projective path and the hop it selects; and the six continuous
error functions of the short test.

Three conventions carry over from the fixed-grid layer and are used again here.
Scalar sizes are Loewner, so the operator norm of a doubled block is its size
against the identity and no norm symbol enters a scalar quantity.  Every
quantity whose finiteness is asserted is extended-real valued.  The reference
text's positive part of a symmetric matrix is its spectral positive part; on the
two matrix-valued occurrences that is the continuous functional calculus of
`x ↦ max x 0`, and on the eight scalar occurrences it is the excess already
carried by the fixed-grid layer.

The canonical metric and the canonical shear are the characterized factors of
the canonical block, taken from the block geometry layer through the flattening
map; nothing here re-derives them, and nothing here depends on how they are
produced beyond the characterization that layer proves.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped ENNReal

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-! ## The canonical block geometry -/

/-- The canonical block `M(E) = E # E^♯` (`e.scale.selection.canonical.metric`),
read on a doubled block through the flattening map. -/
@[expose]
def canonicalBlock (E : BlockMat d) : BlockMat d :=
  ofFullBlockMat (canonBlock (toFullBlockMat E))

/-- The canonical metric `m(E)` (the symmetric and skew factors of the canonical block), the
positive factor
of the unique factorization
`M(E) = G_{-g(E)}^t diag(m(E), m(E)^{-1}) G_{-g(E)}`. -/
@[expose]
def canonicalMetric (E : BlockMat d) : Mat d :=
  canonMetric (toFullBlockMat E)

/-- The canonical shear `g(E)` (the symmetric and skew factors of the canonical block), the skew
factor of the
same factorization. -/
@[expose]
def canonicalShear (E : BlockMat d) : Mat d :=
  canonShear (toFullBlockMat E)

/-- The imbalance `𝔡(E) = |M(E)^{-1/2} E M(E)^{-1/2}|²`
(`e.scale.selection.canonical.metric`). -/
@[expose]
def blockImbalance (E : BlockMat d) : ℝ :=
  canonImbalance (toFullBlockMat E)

/-! ## The determinant account -/

/-- The determinant root `Ξ(E) = det(E)^{1/d}` of a doubled block, the `d`-th
root of the determinant of a `2d`-by-`2d` matrix
(`e.scale.selection.logdet.loss`). -/
@[expose]
def detRoot (d : ℕ) (E : BlockMat d) : ℝ :=
  (toFullBlockMat E).det ^ ((d : ℝ)⁻¹)

/-- The determinant root `Ξ_j^q = Ξ(E_j^q)` of an annealed adapted block. -/
@[expose]
def adaptedDetRoot (P : Measure (CoeffSpace d)) (q : Mat d) (j : ℤ) : ℝ :=
  detRoot d (adaptedMean P q j)

/-- The determinant loss `σ_q(u,v) = log Ξ_u^q - log Ξ_v^q`
(`e.scale.selection.logdet.loss`). -/
@[expose]
def detLoss (P : Measure (CoeffSpace d)) (q : Mat d) (u v : ℤ) : ℝ :=
  Real.log (adaptedDetRoot P q u) - Real.log (adaptedDetRoot P q v)

/-! ## The gap function and the matrix positive part -/

/-- The operator size `‖H‖_op` of a doubled block, in the Loewner form of the
fixed-grid layer: the least `t ≥ 0` with `-tI ≤ H ≤ tI`. -/
@[expose]
def blockOpSize (H : BlockMat d) : ℝ :=
  blockSize H (Book.Ch02.blockIdentity d)

/-- The gap function `𝔤_Q(P) = ‖P‖_op^{Q-1} tr(P - I) + (tr(P - I))^Q`, for
`P ≥ I` (the gap functional of the positive-gap estimate). -/
@[expose]
def gapG (Q : ℝ) (Pm : BlockMat d) : ℝ :=
  blockOpSize Pm ^ (Q - 1) * (blockTrace Pm - 2 * (d : ℝ)) +
    (blockTrace Pm - 2 * (d : ℝ)) ^ Q

/-- The matrix positive part `(H)_+` of a symmetric doubled block: its spectral
positive part, the continuous functional calculus of `x ↦ max x 0`.  This is the
matrix-valued reading of the reference text's positive part, used at the two
sites where the positive part is a matrix rather than a number. -/
@[expose]
def blockPosPart (H : BlockMat d) : BlockMat d :=
  ofFullBlockMat (cfc (fun x : ℝ => max x 0) (toFullBlockMat H))

/-! ## The bridge congruence -/

/-- The bridge congruence `S = H^{1/2} F^{-1/2}` of the near-isometric
comparison (`p.two.grid.transport`, at the bridge data). -/
@[expose]
def bridgeMap (H F : BlockMat d) : FullBlockMat d :=
  matSqrt (toFullBlockMat H) * matSqrt ((toFullBlockMat F)⁻¹)

/-- The Gram matrix `SᵗS` of the bridge congruence. -/
@[expose]
def bridgeGram (H F : BlockMat d) : BlockMat d :=
  ofFullBlockMat ((bridgeMap H F)ᵀ * bridgeMap H F)

/-! ## The transport source coefficients -/

/-- The continued transport coefficient
`𝖣_cont^{tr,S}(q,q') = C_d K(q,q') κ_𝐄 B_q B_{q'} χ_g 𝒰²`, with `𝒰 = 2`
(the source coefficients of the transport estimate). -/
@[expose]
def transportContCoeff (Cd g : ℝ) (E : BlockMat d) (jStar : ℤ) (mu mu' : Mat d) :
    ℝ :=
  Cd * gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') * kappaRef E *
    boundaryConst Cd g mu * boundaryConst Cd g mu' * chiG g * 4

/-- The early transport coefficient
`𝖣_early^{tr,S}(q') = C_d κ_𝐄 B_{q'}² 𝒰²`, with `𝒰 = 2`
(the source coefficients of the transport estimate). -/
@[expose]
def transportEarlyCoeff (Cd g : ℝ) (E : BlockMat d) (mu' : Mat d) : ℝ :=
  Cd * kappaRef E * boundaryConst Cd g mu' ^ 2 * 4

/-- The total transport source coefficient
`𝖣_src^{tr,S} = 1 + 𝖣_cont^{tr,S} + 𝖣_early^{tr,S}`
(the source coefficients of the transport estimate). -/
@[expose]
def transportSrcCoeff (Cd g : ℝ) (E : BlockMat d) (jStar : ℤ) (mu mu' : Mat d) :
    ℝ :=
  1 + transportContCoeff Cd g E jStar mu mu' + transportEarlyCoeff Cd g E mu'

/-- The transported source majorant
`𝓡_src^{tr,S}(q,q';n,j_*) = (𝖣_src^{tr,S} + (𝖣_src^{tr,S})^Q)3^{-a(n-j_*)}`
(the transported source majorant). -/
@[expose]
def transportSrcRemainder (Cd g Q a : ℝ) (E : BlockMat d) (jStar : ℤ)
    (mu mu' : Mat d) (n : ℤ) : ℝ :=
  (transportSrcCoeff Cd g E jStar mu mu' +
      transportSrcCoeff Cd g E jStar mu mu' ^ Q) *
    (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))

/-! ## The bridge source coefficients -/

/-- The continued bridge coefficient
`𝖣_cont^S(p,v;r) = C_d K(p,v) κ_𝐄 B_p B_r χ_g 𝒰²`, with `𝒰 = 2`
(the source coefficients in the two-grid comparison). -/
@[expose]
def bridgeContCoeff (Cd g : ℝ) (E : BlockMat d) (jStar : ℤ)
    (mp mv mr : Mat d) : ℝ :=
  Cd * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) * kappaRef E *
    boundaryConst Cd g mp * boundaryConst Cd g mr * chiG g * 4

/-- The early bridge coefficient `𝖣_early^S(v;r) = C_d κ_𝐄 B_v B_r 𝒰²`, with
`𝒰 = 2` (the source coefficients in the two-grid comparison). -/
@[expose]
def bridgeEarlyCoeff (Cd g : ℝ) (E : BlockMat d) (mv mr : Mat d) : ℝ :=
  Cd * kappaRef E * boundaryConst Cd g mv * boundaryConst Cd g mr * 4

/-- The total bridge source coefficient `𝖣_src^{br,S}(q,q')`: one plus the
maximum of `𝖣_cont^S(p,v;r) + 𝖣_early^S(v;r)` over the two ordered pairs
`(p,v)` and the two terminal grids `r` (the source coefficients in the two-grid comparison).
-/
@[expose]
def bridgeSrcCoeff (Cd g : ℝ) (E : BlockMat d) (jStar : ℤ) (mq mq' : Mat d) :
    ℝ :=
  1 +
    max
      (max (bridgeContCoeff Cd g E jStar mq mq' mq + bridgeEarlyCoeff Cd g E mq' mq)
        (bridgeContCoeff Cd g E jStar mq mq' mq' + bridgeEarlyCoeff Cd g E mq' mq'))
      (max (bridgeContCoeff Cd g E jStar mq' mq mq + bridgeEarlyCoeff Cd g E mq mq)
        (bridgeContCoeff Cd g E jStar mq' mq mq' + bridgeEarlyCoeff Cd g E mq mq'))

/-- The comparison remainder
`𝓡_cmp^S(q,q';v) = C 𝖣_src^{br,S}(q,q')(1 + v - j_*)3^{-ρ_dr(v-j_*)}`
(the source remainder in the two-grid comparison). -/
@[expose]
def bridgeCmpRemainder (C Cd g rhoDr : ℝ) (E : BlockMat d) (jStar : ℤ)
    (mq mq' : Mat d) (v : ℤ) : ℝ :=
  C * bridgeSrcCoeff Cd g E jStar mq mq' * (1 + ((v : ℝ) - (jStar : ℝ))) *
    (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (jStar : ℝ)))

/-- The shifted remainder
`𝓡_sh^S(q,q';n,ℓ) = C 𝖣_src^{br,S}(q,q')3^{ρ_dr ℓ}(1 + n - j_*)3^{-ρ_dr(n-j_*)}`
(`e.two.grid.drift.source.convolution`). -/
@[expose]
def bridgeShiftedRemainder (C Cd g rhoDr : ℝ) (E : BlockMat d) (jStar : ℤ)
    (mq mq' : Mat d) (n l : ℤ) : ℝ :=
  C * bridgeSrcCoeff Cd g E jStar mq mq' * (3 : ℝ) ^ (rhoDr * (l : ℝ)) *
    (1 + ((n : ℝ) - (jStar : ℝ))) *
    (3 : ℝ) ^ (-rhoDr * ((n : ℝ) - (jStar : ℝ)))

/-! ## The two-grid comparison errors -/

/-- The upper comparison error
`ε_+^S(n,ℓ) = CK(3^{-ℓ} + 3^{-(1-ρ_dr)ℓ}D_{q,j_*}(n)) + 𝓡_cmp^S(q,q';n)`
(`e.successful.short.preliminary.comparison`). -/
@[expose]
def bridgeErrUpper (C Cd g rhoDr K : ℝ) (P : Measure (CoeffSpace d))
    (E : BlockMat d) (jStar : ℤ) (mq mq' : Mat d) (n l : ℤ) : ℝ :=
  C * K *
      ((3 : ℝ) ^ (-(l : ℝ)) +
        (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
          linearDrift P rhoDr (roundedGrid jStar mq) jStar n) +
    bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' n

/-- The lower comparison error
`ε_-^S(n,ℓ) = CK(1-CK3^{-ℓ})^{-1}(3^{-ℓ} + 3^{-(1-ρ_dr)ℓ}D_{q,j_*}(n+ℓ))
+ 𝓡_cmp^S(q',q;n+ℓ)` (`e.successful.short.preliminary.comparison`). -/
@[expose]
def bridgeErrLower (C Cd g rhoDr K : ℝ) (P : Measure (CoeffSpace d))
    (E : BlockMat d) (jStar : ℤ) (mq mq' : Mat d) (n l : ℤ) : ℝ :=
  C * K / (1 - C * K * (3 : ℝ) ^ (-(l : ℝ))) *
      ((3 : ℝ) ^ (-(l : ℝ)) +
        (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
          linearDrift P rhoDr (roundedGrid jStar mq) jStar (n + l)) +
    bridgeCmpRemainder C Cd g rhoDr E jStar mq' mq (n + l)

/-! ## The constant-speed projective path and the hop it selects -/

/-- The real power `A^θ` of a positive matrix, by the continuous functional
calculus. -/
@[expose]
def matPow (theta : ℝ) (A : Mat d) : Mat d :=
  cfc (fun x : ℝ => x ^ theta) A

/-- The constant-speed projective path
`m(θ) = m₀^{1/2}(m₀^{-1/2}m₁m₀^{-1/2})^θ m₀^{1/2}`
(`e.renormalization.geometry.update`). -/
@[expose]
def projPath (m0 m1 : Mat d) (theta : ℝ) : Mat d :=
  matSqrt m0 * matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) * matSqrt m0

/-- The next point on the fixed constant-speed path from `m₀` to `m₁` at
projective distance at most `c`: the path point at parameter
`min{c/d_pr([m₀],[m₁]), 1}`, and the endpoint `m₁` when the two projective
classes agree (`p.successful.short.bridge`, at the candidate
construction). -/
@[expose]
def projPathStep (c : ℝ) (m0 m1 : Mat d) : Mat d :=
  if projDist m0 m1 = 0 then m1
  else projPath m0 m1 (min (c / projDist m0 m1) 1)

/-! ## The six continuous error functions of the short test -/

/-- `d_n(b,δ) = (1+δ)^d 3^{-ρ_dr ℓ₀} b + 2d((1+δ)^d - 1)`, the new-scale drift
envelope of the short test (`p.successful.short.bridge`, first of the
six error functions). -/
@[expose]
def shortDriftNew (d : ℕ) (rhoDr : ℝ) (l0 : ℤ) (b delta : ℝ) : ℝ :=
  (1 + delta) ^ d * (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) * b +
    2 * (d : ℝ) * ((1 + delta) ^ d - 1)

/-- `d_t(b,δ) = (1+δ)^d 3^{-2ρ_dr ℓ₀} b + 2d((1+δ)^d - 1)`, the terminal-scale
drift envelope of the short test (second of the six). -/
@[expose]
def shortDriftTerm (d : ℕ) (rhoDr : ℝ) (l0 : ℤ) (b delta : ℝ) : ℝ :=
  (1 + delta) ^ d * (3 : ℝ) ^ (-2 * rhoDr * (l0 : ℝ)) * b +
    2 * (d : ℝ) * ((1 + delta) ^ d - 1)

/-- `e_+(b,δ,R₁) = CK_hop(3^{-ℓ₀} + 3^{-(1-ρ_dr)ℓ₀}d_n(b,δ)) + R₁`, the upper
comparison envelope of the short test (third of the six). -/
@[expose]
def shortErrUpper (d : ℕ) (C Khop rhoDr : ℝ) (l0 : ℤ) (b delta R1 : ℝ) : ℝ :=
  C * Khop *
      ((3 : ℝ) ^ (-(l0 : ℝ)) +
        (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) * shortDriftNew d rhoDr l0 b delta) +
    R1

/-- `e_-(b,δ,R₂) = CK_hop(1 - CK_hop3^{-ℓ₀})^{-1}(3^{-ℓ₀}
+ 3^{-(1-ρ_dr)ℓ₀}d_t(b,δ)) + R₂`, the lower comparison envelope of the short
test (fourth of the six). -/
@[expose]
def shortErrLower (d : ℕ) (C Khop rhoDr : ℝ) (l0 : ℤ) (b delta R2 : ℝ) : ℝ :=
  C * Khop / (1 - C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) *
      ((3 : ℝ) ^ (-(l0 : ℝ)) +
        (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) * shortDriftTerm d rhoDr l0 b delta) +
    R2

/-- `η_br(b,δ,R₁,R₂) = max{e_-(b,δ,R₂), (1 + e_+(b,δ,R₁))(1+δ)^d - 1}`, the
bridge-error envelope of the short test (fifth of the six). -/
@[expose]
def shortBridgeErr (d : ℕ) (C Khop rhoDr : ℝ) (l0 : ℤ) (b delta R1 R2 : ℝ) :
    ℝ :=
  max (shortErrLower d C Khop rhoDr l0 b delta R2)
    ((1 + shortErrUpper d C Khop rhoDr l0 b delta R1) * (1 + delta) ^ d - 1)

/-- `𝔡_new(b,δ,R₂,R₃) = C(e_-(b,δ,R₂) + K_hop3^{-ℓ₀}
+ (1+K_hop)3^{2ρ_dr ℓ₀}d_t(b,δ) + R₃)`, the new-grid drift envelope of the short
test (sixth of the six).  The reference text displays this envelope with a
further argument that its body never reads; the display is a typo for the
four-argument form written here, and the source correction is recorded. -/
@[expose]
def shortNewDrift (d : ℕ) (C Khop rhoDr : ℝ) (l0 : ℤ) (b delta R2 R3 : ℝ) : ℝ :=
  C *
    (shortErrLower d C Khop rhoDr l0 b delta R2 + Khop * (3 : ℝ) ^ (-(l0 : ℝ)) +
      (1 + Khop) * (3 : ℝ) ^ (2 * rhoDr * (l0 : ℝ)) *
        shortDriftTerm d rhoDr l0 b delta +
      R3)

end

end HighContrast
end HCPolySupport
