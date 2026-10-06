/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdaptedTilt
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionAdapters

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastIsotropyCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the boundary comparison the corresponding clause: the isotropy carriers

the corresponding argument the boundary comparison the corresponding clause replace three scalar
carriers of the Euclidean boundary
envelope:

| carrier | established value | the corresponding argument target |
|---|---|---|
| `inflatedReference Cd g m G E` | `blockScale (2·boundaryConst·3^{gG}) 𝐄` | `blockScale cIso 𝐄` |
| `weakLoadScale Cd g m G kap` | `2·(boundaryConst·3^{gG})·kap·7` | `2·cIso·kap·7` |
| `kap2Value Cd g m G 𝐄` | `κ_𝐄·(2·boundaryConst·3^{gG})` | `(1 - cIso)⁻¹` |

**A refutation first.**  The alternative formulation states these rows as
*monotonicity in the envelope*, under
hypotheses of the form

```
2·boundaryConst Cd g m_Al·3^{g((t+G)-s)} ≤ cIso·3^{g(t-s)}      (the row)
boundaryConst Cd g n·3^{gG} ≤ cIso                              (the load, kap2)
```

and its docstring expects the isotropy comparison's isotropy comparison to discharge them.  **It
does not, and nothing can at a `Π`-free `cIso`.**  Those hypotheses are
statements about the *deterministic geometric constants* — no annealed block
occurs in them — whereas the isotropy comparison bounds `adaptedMean`.  The
row-envelope eccentricity bound
and the row-envelope eccentricity bounds below establish that any `cIso`
meeting them is at least (twice) `witnessEccentricity m_Al`, which is unbounded
on the admissible class.  The alternative formulation's lemmas
are sound but their hypothesis is only satisfiable at the `Π`-dependent value it
was meant to replace.

**The correct interface.**  What the boundary comparison actually needs is not a scalar bound on
`boundaryConst·3^{gG}` but a *change of normalizing block*: the three carriers
are all the same formula evaluated at the reference inflation scalar, and the
substitution is `2·boundaryConst·3^{gG} ↦ 1 + cIso`.  This file exhibits that
factorization (`referenceOfScalar`, `loadScaleOfScalar`), defines the three
isotropy carriers at the isotropy comparison's constant, and proves the facts their consumers
need directly from the isotropy comparison's two-sided comparison — the envelope, the
comparability, and the normalization `Λ(𝐄; F)`.

**The residual the formulation names is also closed here.**  `SmallContrastLoadScalePiFree`
records that a dimension-only bound on `kappaRef 𝐄` is "a new named input for
the isotropy construction".  The corrected
`Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one_of_coarseEllipticityDagger`
is established and available, and `kappaRef_le_of_refContrast_le` /
`sqrt_kappaRef_le_of_refContrast_le` below put it in the shape the metric
factor's `r` slot consumes.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The obstruction: the alternative formulation's envelope hypotheses force `Π` -/

/-! ## The factorization: the carriers depend on the reference scalar only -/

/-- The normalizing block as a function of the reference inflation scalar. -/
@[expose]
def referenceOfScalar (c : ℝ) (E : BlockMat d) : BlockMat d := blockScale c E

/-- The load scale as a function of the reference inflation scalar. -/
@[expose]
def loadScaleOfScalar (c kap : ℝ) : ℝ := c * kap * 7

/-! ## The isotropy carriers -/

/-- **the corresponding clause.**  The normalizing block at the isotropy comparison's isotropy
constant: the
substitution `2·boundaryConst·3^{gG} ↦ 1 + cIso` in the inflated reference. -/
@[expose]
def isotropyReference (cIso : ℝ) (E : BlockMat d) : BlockMat d :=
  referenceOfScalar (1 + cIso) E

/-- **the corresponding clause.**  The load scale at the isotropy comparison's isotropy constant. -/
@[expose]
def isotropyLoadScale (cIso kap : ℝ) : ℝ := loadScaleOfScalar (1 + cIso) kap

/-- **the corresponding clause.**  The entry comparability constant at the isotropy comparison's
isotropy constant.
Note that `kappaRef 𝐄` has disappeared: the isotropy comparison's lower bound already carries the
reference imbalance inside `nearIdentityDefect`. -/
@[expose]
def isotropyKap2 (cIso : ℝ) : ℝ := (1 - cIso)⁻¹

theorem isotropyReference_eq_blockScale (cIso : ℝ) (E : BlockMat d) :
    isotropyReference cIso E = blockScale (1 + cIso) E := rfl

theorem isSymmetricBlockMat_isotropyReference {E : BlockMat d} (cIso : ℝ)
    (hE : IsSymmetricBlockMat E) :
    IsSymmetricBlockMat (isotropyReference cIso E) :=
  isSymmetricBlockMat_blockScale _ hE

theorem blockPosDef_isotropyReference {E : BlockMat d} {cIso : ℝ}
    (hcIso : 0 ≤ cIso) (hEpd : BlockPosDef E) :
    BlockPosDef (isotropyReference cIso E) :=
  Transport.blockPosDef_blockScale (by linarith only [hcIso]) hEpd

/-! ## What the consumers need, from the isotropy comparison -/

/-- **The normalization `Λ(𝐄; F)` at the isotropy reference.**  The established
account carries `blockSize E (inflatedReference …)`, which is `Π`-dependent
through the envelope; at the isotropy reference it is at most `(1 + cIso)⁻¹`,
hence at most one, with no geometric input at all. -/
theorem blockSize_reference_isotropyReference_le {E : BlockMat d} {cIso : ℝ}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) (hcIso : 0 ≤ cIso) :
    blockSize E (isotropyReference cIso E) ≤ (1 + cIso)⁻¹ := by
  have hpos : (0 : ℝ) < 1 + cIso := by linarith only [hcIso]
  refine Transport.blockSize_le_of_blockMatLoewnerLE_blockScale hE
    (posDef_toFullBlockMat hE hEpd).posSemidef
    (isSymmetricBlockMat_isotropyReference cIso hE)
    (blockPosDef_isotropyReference hcIso hEpd)
    (inv_nonneg.mpr hpos.le) ?_
  intro X
  rw [isotropyReference_eq_blockScale, Sharp.blockVecDot_blockMatVecMul_blockScale,
    Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hcancel : (1 + cIso)⁻¹ * ((1 + cIso) * blockVecDot X (blockMatVecMul E X)) =
      blockVecDot X (blockMatVecMul E X) := by
    rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  rw [hcancel]

/-- **The envelope slot at the isotropy reference**, from the isotropy comparison's upper half. -/
theorem le_isotropyReference_of_near_reference {A E : BlockMat d} {cIso : ℝ}
    (hupp : BlockMatLoewnerLE A (blockScale (1 + cIso) E)) :
    BlockMatLoewnerLE A (isotropyReference cIso E) := hupp

/-- **The comparability slot at the isotropy constant**, from the isotropy comparison's lower
half.  This is the `Π`-free replacement of `kap2Value`. -/
theorem le_isotropyKap2_smul_of_near_reference {A E : BlockMat d} {cIso : ℝ}
    (hsmall : cIso < 1)
    (hlow : BlockMatLoewnerLE (blockScale (1 - cIso) E) A) :
    BlockMatLoewnerLE E (blockScale (isotropyKap2 cIso) A) := by
  have hpos : (0 : ℝ) < 1 - cIso := by linarith only [hsmall]
  intro X
  have h := hlow X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale, isotropyKap2]
  have hstep : (1 - cIso) * blockVecDot X (blockMatVecMul E X) ≤
      blockVecDot X (blockMatVecMul A X) := by linarith only [h]
  have hmul := mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hpos.le)
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at hmul
  linarith only [hmul]

/-! ## The reference imbalance is dimension-only -/

/-- **The input `SmallContrastLoadScalePiFree` names as missing.**  Under the
small-contrast premise the reference imbalance is bounded by a dimension-only
quantity obtained from the corrected reference comparison. -/
theorem kappaRef_le_of_refContrast_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sigma : ℝ} (hsigma : refContrast E - 1 ≤ sigma) :
    kappaRef E ≤ 1 + 6 * sigma := by
  have h :=
    Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one_of_coarseEllipticityDagger
      hdag
  linarith only [h, hsigma]

/-- The metric factor's `r` slot at a dimension-only value. -/
theorem sqrt_kappaRef_le_of_refContrast_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sigma : ℝ} (hsigma : refContrast E - 1 ≤ sigma) :
    Real.sqrt (kappaRef E) ≤ Real.sqrt (1 + 6 * sigma) :=
  Real.sqrt_le_sqrt (kappaRef_le_of_refContrast_le hdag hsigma)

/-! ## The three rows at the adapted mean -/

/-- **the corresponding clause and 5 at the terminal mean.**  The two slots the corresponding step
consumes, at
constants free of `boundaryConst`, `witnessEccentricity`, `3^{gG}` and
`kappaRef`. -/
theorem isotropy_carriers_at_terminal [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {k r : ℤ} {G : ℕ} (hk0 : 0 ≤ k)
    {sigma cEnt : ℝ} (hsigma : refContrast E - 1 ≤ sigma) (hsigma0 : 0 ≤ sigma)
    (hcEnt : 0 < cEnt) (hsmall : nearIdentityDefect cEnt sigma < 1)
    (hkthr : euclideanEntryThreshold K (cEnt / 2) sK ≤ k)
    (hgap : tiltGap Cd g (cEnt / 2) nu G ≤ r - k)
    (hDelta : 0 ≤ r + (G : ℤ) - 1 - sK)
    (hentry : sourceMomentTwo K ≤ (3 : ℝ) ^ (r + (G : ℤ) - sK))
    (hsub : adaptedCell (roundedGrid l nu) r ⊆ centeredCube d (r + (G : ℤ)))
    (hint : HasFiniteAdaptedMean P (roundedGrid l nu) r) :
    BlockMatLoewnerLE (adaptedMean P (roundedGrid l nu) r)
        (isotropyReference (nearIdentityDefect cEnt sigma) E) ∧
      BlockMatLoewnerLE E
        (blockScale (isotropyKap2 (nearIdentityDefect cEnt sigma))
          (adaptedMean P (roundedGrid l nu) r)) ∧
      blockSize E (isotropyReference (nearIdentityDefect cEnt sigma) E) ≤
        (1 + nearIdentityDefect cEnt sigma)⁻¹ := by
  obtain ⟨hlow, hupp⟩ := adaptedMean_near_reference hd hg hdag hstat hl hCd hnu
    hsK hk0 hsigma hsigma0 hcEnt hkthr hgap hDelta hentry hsub hint
  refine ⟨le_isotropyReference_of_near_reference hupp,
    le_isotropyKap2_smul_of_near_reference hsmall hlow, ?_⟩
  exact blockSize_reference_isotropyReference_le hdag.refBlock_isSymm
    hdag.refBlock_posDef (nearIdentityDefect_nonneg hcEnt.le hsigma0)

end

end HCPolySupport.HighContrast.Quenched
