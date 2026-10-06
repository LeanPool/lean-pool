/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeReferenceComparison
public import LeanPool.HighContrastHomogenization.Provider.Quenched.BlockScaleGeometry
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.ReferenceIntermediate
public import LeanPool.HighContrastHomogenization.Annealed.Integrability

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHomogenizedComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reference-normalized near-identity comparison

This file formalizes the printed comparison HC (4.18),

> for every `m ≥ 2n₁`,   `|𝐄^{-1/2}𝐀hom(cus_m)𝐄^{-1/2} - I_{2d}| ≤ c(d)`,

in the construction's Loewner dialect, where the printed absolute-value statement
reads `blockScale (1 - c) 𝐄 ≤ 𝐀hom ≤ blockScale (1 + c) 𝐄`.

The printed derivation has two halves and this file supplies both, in the
generality in which they are actually printed.

* **The algebraic half** is Lemma 2.7 of HC (equation (2.89), the printed
  argument): *a one-sided bound gives a two-sided bound for free when the
  reference contrast is small.*  The printed proof reads the chain
  `𝐄_* ≤ 𝐀_*(U) ≤ 𝐀(U) ≤ 𝐄₁` and then quotes the upper half of HC (2.82).
  That upper half is machine-refuted as printed (the corrected statement, the upper comparison
  obstruction),
  so the valid route uses the reference ratio bound `κ_𝐄 ≤ 1 + 6(Θ - 1)` of
  `Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one`, which is the established
  replacement for the false display.  Given `A ≤ (1 + ε)𝐄`, the sharp
  involution reverses the order and is homogeneous of degree minus one, the
  annealed block dominates its own sharp, and `𝐄 ≤ κ_𝐄𝐄^♯`; the four facts
  compose to `((1 + ε)κ_𝐄)^{-1}𝐄 ≤ A`.  No `Π` enters.

* **The analytic half** is the Euclidean-cube envelope HC (2.98), the printed
  argument, whose upper part is `𝐀hom(cu_n) ≤ (1 + 3^{3-n}K_{Ψ_S}²)𝐄`.
  Here it is proved directly from `e.coarse.ellipticity` at coincident
  scales — where the Dagger's discount is exactly `1`, with no boundary
  transfer and therefore no `boundaryConst` — plus the Markov step on the
  source scale that the construction already uses elsewhere.  The resulting defect is
  `M₂(K)·3^{-(n - s_K)}`, so the scale threshold it forces is
  `n ≳ s_K + log₃ M₂(K) ≈ 4 log₃ K_bar_S`: exactly the `4 log K_{Ψ_S}` term of the
  printed `n₁` (the printed argument).

Both halves are free of the reference aspect ratio `Π`: the whole point of the
printed route is that `Π` enters only through the scale threshold, which is the
design principle stated at the printed argument and the slot the frozen `hcore` binder
reserves for it.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The algebraic half: two-sided bounds from one-sided bounds -/

/-- **Lemma 2.7 of HC, lower half** (equation (2.89)).  A positive block that
dominates its own sharp and is dominated by `c𝐄` is bounded below by
`(cκ_𝐄)^{-1}𝐄`.  The printed proof reads the chain
`𝐄_* ≤ 𝐀_*(U) ≤ 𝐀(U) ≤ 𝐄₁` and quotes HC (2.82); the route here composes the
order reversal of the sharp involution, its degree `-1` homogeneity, the
self-domination `A^♯ ≤ A`, and the intrinsic bound `𝐄 ≤ κ_𝐄𝐄^♯`. -/
theorem blockScale_inv_le_of_le_blockScale [NeZero d] {E A : BlockMat d}
    (hEsymm : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hEsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hAsymm : IsSymmetricBlockMat A) (hApd : BlockPosDef A)
    (hAself : BlockMatLoewnerLE (blockSharp A) A)
    {c : ℝ} (hc : 0 < c)
    (hupper : BlockMatLoewnerLE A (blockScale c E)) :
    BlockMatLoewnerLE (blockScale (c * kappaRef E)⁻¹ E) A := by
  have hkap1 : (1 : ℝ) ≤ kappaRef E := Initialization.one_le_kappaRef hEsymm hEpd hEsharp
  have hkap0 : (0 : ℝ) < kappaRef E := lt_of_lt_of_le zero_lt_one hkap1
  have hscaleSymm : IsSymmetricBlockMat (blockScale c E) :=
    isSymmetricBlockMat_blockScale c hEsymm
  have hscalePd : BlockPosDef (blockScale c E) := Transport.blockPosDef_blockScale hc hEpd
  have hrev := blockMatLoewnerLE_blockSharp_of_le hAsymm hscaleSymm hApd hscalePd hupper
  rw [blockSharp_blockScale hEsymm hEpd hc] at hrev
  have hkR := Initialization.blockMatLoewnerLE_reference_kappaRef_blockSharp hEsymm hEpd
  intro X
  have h1 := hkR X
  have h2 := hrev X
  have h3 := hAself X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h1 h2
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  have e1 : blockVecDot X (blockMatVecMul E X) ≤
      kappaRef E * blockVecDot X (blockMatVecMul (blockSharp E) X) := by
    linarith only [h1]
  have e2 : c⁻¹ * blockVecDot X (blockMatVecMul (blockSharp E) X) ≤
      blockVecDot X (blockMatVecMul (blockSharp A) X) := by
    linarith only [h2]
  have e3 : blockVecDot X (blockMatVecMul (blockSharp A) X) ≤
      blockVecDot X (blockMatVecMul A X) := by
    linarith only [h3]
  have hstep : (kappaRef E)⁻¹ * blockVecDot X (blockMatVecMul E X) ≤
      blockVecDot X (blockMatVecMul (blockSharp E) X) := by
    have h := mul_le_mul_of_nonneg_left e1 (inv_nonneg.mpr hkap0.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hkap0.ne', one_mul] at h
  have hstep2 : c⁻¹ * ((kappaRef E)⁻¹ * blockVecDot X (blockMatVecMul E X)) ≤
      c⁻¹ * blockVecDot X (blockMatVecMul (blockSharp E) X) :=
    mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hc.le)
  have hfinal : (c * kappaRef E)⁻¹ * blockVecDot X (blockMatVecMul E X) ≤
      blockVecDot X (blockMatVecMul A X) := by
    rw [mul_inv]
    calc
      c⁻¹ * (kappaRef E)⁻¹ * blockVecDot X (blockMatVecMul E X) =
          c⁻¹ * ((kappaRef E)⁻¹ * blockVecDot X (blockMatVecMul E X)) := by ring
      _ ≤ c⁻¹ * blockVecDot X (blockMatVecMul (blockSharp E) X) := hstep2
      _ ≤ blockVecDot X (blockMatVecMul (blockSharp A) X) := e2
      _ ≤ blockVecDot X (blockMatVecMul A X) := e3
  linarith only [hfinal]

/-- The near-identity defect assembled from the entry defect `ε` of the
one-sided envelope and the reference contrast excess `σ`: the printed `c(d)` of
HC (4.18), which the print obtains by choosing `A(d)` large and
`σ_0(d)` small. -/
@[expose]
def nearIdentityDefect (eps sigma : ℝ) : ℝ :=
  (1 + eps) * (1 + 6 * sigma) - 1

theorem nearIdentityDefect_nonneg {eps sigma : ℝ} (heps : 0 ≤ eps)
    (hsigma : 0 ≤ sigma) : 0 ≤ nearIdentityDefect eps sigma := by
  rw [nearIdentityDefect]
  nlinarith only [heps, hsigma]

/-- **Lemma 2.7 of HC** (equation (2.89)): the two-sided near-identity
comparison from a one-sided envelope.  This is the algebraic engine of
HC (4.18). -/
theorem near_identity_of_le_blockScale [NeZero d] {E A : BlockMat d}
    (hEsymm : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hEsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hAsymm : IsSymmetricBlockMat A) (hApd : BlockPosDef A)
    (hAself : BlockMatLoewnerLE (blockSharp A) A)
    {eps cIso : ℝ} (heps : 0 ≤ eps) (hcIso : 0 ≤ cIso)
    (hupper : BlockMatLoewnerLE A (blockScale (1 + eps) E))
    (hprod : (1 + eps) * kappaRef E ≤ 1 + cIso) :
    BlockMatLoewnerLE (blockScale (1 - cIso) E) A ∧
      BlockMatLoewnerLE A (blockScale (1 + cIso) E) := by
  have hkap1 : (1 : ℝ) ≤ kappaRef E := Initialization.one_le_kappaRef hEsymm hEpd hEsharp
  have heps0 : (0 : ℝ) < 1 + eps := by linarith only [heps]
  have hupperScalar : (1 : ℝ) + eps ≤ 1 + cIso := by
    nlinarith only [hprod, hkap1, heps0]
  refine ⟨?_, hupper.trans (blockMatLoewnerLE_blockScale_of_scalar_le hupperScalar hEpd)⟩
  have hlow := blockScale_inv_le_of_le_blockScale hEsymm hEpd hEsharp hAsymm hApd
    hAself heps0 hupper
  refine (blockMatLoewnerLE_blockScale_of_scalar_le ?_ hEpd).trans hlow
  have hprod0 : (0 : ℝ) < (1 + eps) * kappaRef E :=
    mul_pos heps0 (lt_of_lt_of_le zero_lt_one hkap1)
  have hcIso0 : (0 : ℝ) < 1 + cIso := by linarith only [hcIso]
  have hcancel : (1 - cIso) * (1 + cIso) ≤ 1 := by nlinarith only [hcIso]
  have hstep : (1 - cIso) * ((1 + eps) * kappaRef E) ≤ 1 := by
    rcases le_or_gt (1 - cIso) 0 with hneg | hpos
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hneg hprod0.le) zero_le_one
    · exact le_trans (mul_le_mul_of_nonneg_left hprod hpos.le) hcancel
  have h := mul_le_mul_of_nonneg_right hstep (inv_nonneg.mpr hprod0.le)
  rwa [mul_assoc, mul_inv_cancel₀ hprod0.ne', mul_one, one_mul] at h

/-! ## The analytic half: the Euclidean annealed envelope -/

/-- The pathwise Euclidean envelope at a burn scale: the coarse response of the
centered cube of scale `n` is dominated by `3^{g(m-n)}𝐄` whenever the source has
burned at a scale `m ≥ n`.  At `m = n` the discount is exactly `1` — the
coincident-scale reading of `e.coarse.ellipticity` that costs no boundary
transfer. -/
private theorem coarseBlock_centeredCube_le_of_burn {g : ℝ} {E : BlockMat d}
    {S : CoeffSpace d → ℝ} {a : CoeffSpace d}
    (hbound : ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
      standardCellCenter k w ∈ centeredCube d m →
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
        (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E))
    {n m : ℤ} (hnm : n ≤ m) (hm : S a ≤ (3 : ℝ) ^ m) :
    BlockMatLoewnerLE (coarseBlock (centeredCube d n) a)
      (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (n : ℝ)))) E) := by
  have h := hbound m hm n hnm 0 (standardCellCenter_zero_mem_centeredCube n m)
  rwa [standardCell_zero] at h

/-- The entry defect of the Euclidean annealed envelope: the construction's rendering
of the printed `3^{3-n}K_{Ψ_S}²` of HC (2.98). -/
@[expose]
def euclideanEntryDefect (K : ℝ) (sK n : ℤ) : ℝ :=
  sourceMomentTwo K * (3 : ℝ) ^ (sK - n)

/-- **The Euclidean annealed envelope** (HC (2.98), upper half):
`𝐀hom(cu_n) ≤ (1 + M₂(K)3^{-(n-s_K)})𝐄`, with prefactor exactly one and a
defect that decays geometrically in the scale.  No aspect-ratio constant
appears: the Dagger is read at coincident scales, so no adapted-cell boundary
transfer is performed. -/
theorem annealedBlock_centeredCube_le_one_add_entryDefect [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {n : ℤ} (hDelta : 0 ≤ n - 1 - sK) :
    BlockMatLoewnerLE (annealedBlock P (centeredCube d n))
      (blockScale (1 + euclideanEntryDefect K sK n) E) := by
  classical
  have hg := hdag.g_mem
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  set bad : Set (CoeffSpace d) := {a | (3 : ℝ) ^ n < S a} with hbaddef
  have hbadmeas : MeasurableSet bad :=
    measurableSet_lt measurable_const hdag.source_measurable
  have hnss1 : ∀ a, 1 ≤ nss a := fun a => one_le_normalizedSourceScale S sK a
  have hquadE : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul E X) := by
    intro X
    by_cases hX : X = 0
    · subst X
      simp [blockMatVecMul, blockVecDot, vecDot]
    · exact (hdag.refBlock_posDef X hX).le
  -- the pathwise majorant
  have hscalar : ∀ᵐ a ∂P, ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul (coarseBlock (centeredCube d n) a) X) ≤
        (1 + bad.indicator nss a) * blockVecDot X (blockMatVecMul E X) := by
    filter_upwards [hdag.coarse_bound] with a hbound
    intro X
    by_cases hS : S a ≤ (3 : ℝ) ^ n
    · -- good event: the Dagger at coincident scales, discount one
      have hcell := coarseBlock_centeredCube_le_of_burn hbound (le_refl n) hS X
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell
      have hzero : (3 : ℝ) ^ (g * ((n : ℝ) - (n : ℝ))) = 1 := by
        rw [sub_self, mul_zero, Real.rpow_zero]
      rw [hzero] at hcell
      have hind : bad.indicator nss a = 0 := by
        refine Set.indicator_of_notMem ?_ nss
        rw [hbaddef, Set.mem_ofPred_eq]
        exact not_lt.mpr hS
      rw [hind]
      linarith only [hcell, hquadE X]
    · -- bad event: the crude branch at the source's own scale
      push Not at hS
      have hS0 : 0 < S a := lt_trans (zpow_pos (by norm_num) _) hS
      set m : ℤ := ⌈Real.logb 3 (S a)⌉ with hmdef
      have hlogS : ((n : ℤ) : ℝ) < Real.logb 3 (S a) := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) hS0]
        rw [← Real.rpow_intCast (3 : ℝ) n] at hS
        exact hS
      have hm1 : n ≤ m := by
        have h := le_trans hlogS.le (Int.le_ceil (Real.logb 3 (S a)))
        exact_mod_cast h
      have hm2 : S a ≤ (3 : ℝ) ^ m := by
        have h1 : S a = (3 : ℝ) ^ Real.logb 3 (S a) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hS0).symm
        rw [h1, ← Real.rpow_intCast (3 : ℝ) m]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)
      have hcell := coarseBlock_centeredCube_le_of_burn hbound hm1 hm2 X
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell
      have hup : (m : ℝ) ≤ Real.logb 3 (S a) + 1 := by
        have h := Int.ceil_lt_add_one (Real.logb 3 (S a))
        exact_mod_cast h.le
      have hmS : (3 : ℝ) ^ ((m : ℝ) - (n : ℝ)) ≤ nss a := by
        have h1 : (3 : ℝ) ^ ((m : ℝ) - (n : ℝ)) ≤
            (3 : ℝ) ^ (Real.logb 3 (S a) + 1 - (n : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          linarith only [hup]
        refine h1.trans ?_
        have h2 : (3 : ℝ) ^ (Real.logb 3 (S a) + 1 - (n : ℝ)) =
            S a * (3 : ℝ) ^ (1 - (n : ℝ)) := by
          rw [show Real.logb 3 (S a) + 1 - (n : ℝ) =
              Real.logb 3 (S a) + (1 - (n : ℝ)) from by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 3),
            Real.rpow_logb (by norm_num) (by norm_num) hS0]
        rw [h2]
        have h3 : S a * (3 : ℝ) ^ (1 - (n : ℝ)) ≤ S a * (3 : ℝ) ^ (-(sK : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hS0.le
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have hcast : (0 : ℝ) ≤ ((n - 1 - sK : ℤ) : ℝ) := by exact_mod_cast hDelta
          push_cast at hcast ⊢
          linarith only [hcast]
        refine h3.trans ?_
        rw [show (3 : ℝ) ^ (-(sK : ℝ)) = (3 : ℝ) ^ (-sK : ℤ) from by
          rw [← Real.rpow_intCast (3 : ℝ) (-sK)]
          norm_num]
        rw [hnssdef, normalizedSourceScale]
        exact le_max_right _ _
      have hfactor : (3 : ℝ) ^ (g * ((m : ℝ) - (n : ℝ))) ≤ nss a := by
        calc
          (3 : ℝ) ^ (g * ((m : ℝ) - (n : ℝ))) =
              ((3 : ℝ) ^ ((m : ℝ) - (n : ℝ))) ^ g := by
            rw [mul_comm g, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
          _ ≤ nss a ^ g :=
            Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hmS hg.1
          _ ≤ nss a ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (hnss1 a) hg.2.le
          _ = nss a := Real.rpow_one _
      have hind : bad.indicator nss a = nss a := by
        refine Set.indicator_of_mem ?_ nss
        rw [hbaddef, Set.mem_ofPred_eq]
        exact hS
      rw [hind]
      have hnss0 : 0 ≤ nss a := le_trans zero_le_one (hnss1 a)
      nlinarith only [hcell, hfactor, hquadE X, hnss0]
  -- the indicator's first moment
  set tau : ℝ := (3 : ℝ) ^ (n - sK) with htaudef
  have htau0 : 0 < tau := zpow_pos (by norm_num) _
  have hnss_tau : ∀ a ∈ bad, tau ≤ nss a := by
    intro a ha
    rw [hbaddef, Set.mem_ofPred_eq] at ha
    have h1 : tau * (3 : ℝ) ^ sK ≤ S a := by
      rw [htaudef, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      have heq : n - sK + sK = n := by ring
      rw [heq]
      exact ha.le
    have h2 : tau ≤ S a * (3 : ℝ) ^ (-sK) := by
      calc
        tau = tau * (3 : ℝ) ^ sK * (3 : ℝ) ^ (-sK) := by
          rw [mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp
        _ ≤ S a * (3 : ℝ) ^ (-sK) := by
          refine mul_le_mul_of_nonneg_right h1 ?_
          positivity
    refine le_trans h2 ?_
    rw [hnssdef, normalizedSourceScale]
    exact le_max_right _ _
  have hindsq : ∀ a, bad.indicator nss a ≤ tau⁻¹ * nss a ^ 2 := by
    intro a
    by_cases ha : a ∈ bad
    · rw [Set.indicator_of_mem ha]
      have h1 := hnss_tau a ha
      have hnss0 : 0 ≤ nss a := le_trans zero_le_one (hnss1 a)
      rw [← sub_nonneg] at h1
      rw [← sub_nonneg]
      have hkey : tau⁻¹ * nss a ^ 2 - nss a = tau⁻¹ * (nss a * (nss a - tau)) := by
        field_simp
      rw [hkey]
      exact mul_nonneg (inv_nonneg.mpr htau0.le)
        (mul_nonneg hnss0 (by linarith only [h1]))
    · rw [Set.indicator_of_notMem ha]
      positivity
  have hindint : Integrable (fun a => bad.indicator nss a) P := by
    refine (Integrable.indicator ?_ hbadmeas).congr
      (_root_.Filter.Eventually.of_forall fun a => rfl)
    exact integrable_normalizedSourceScale hdag hsK
  have hindmom : ∫ a, bad.indicator nss a ∂P ≤ euclideanEntryDefect K sK n := by
    have h1 : ∫ a, bad.indicator nss a ∂P ≤ ∫ a, tau⁻¹ * nss a ^ 2 ∂P := by
      refine integral_mono hindint ?_ hindsq
      exact (integrable_sq_normalizedSourceScale hdag hsK).const_mul _
    refine le_trans h1 ?_
    rw [integral_const_mul]
    have h2 := integral_sq_normalizedSourceScale_le hdag hsK
    have h3 : tau⁻¹ * (∫ a, nss a ^ 2 ∂P) ≤ tau⁻¹ * sourceMomentTwo K :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr htau0.le)
    refine le_trans h3 (le_of_eq ?_)
    rw [euclideanEntryDefect, htaudef, ← zpow_neg]
    have heq : -(n - sK) = sK - n := by ring
    rw [heq]
    ring
  -- integrate
  intro X
  have hint : HasIntegrableCoarseBlock P (centeredCube d n) :=
    hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag n
  have hid := blockVecDot_blockMatVecMul_annealedBlock hint X
  rw [hid, Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hint1 : Integrable
      (fun a => blockVecDot X (blockMatVecMul (coarseBlock (centeredCube d n) a) X)) P :=
    integrable_blockVecDot_coarseBlock hint X
  have hint2 : Integrable (fun a => (1 + bad.indicator nss a) *
      blockVecDot X (blockMatVecMul E X)) P := by
    have h := ((integrable_const (1 : ℝ)).add hindint).mul_const
      (blockVecDot X (blockMatVecMul E X))
    refine h.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.add_apply]
  have hmono := integral_mono_ae hint1 hint2 (by
    filter_upwards [hscalar] with a ha using ha X)
  have hsplit : ∫ a, (1 + bad.indicator nss a) *
      blockVecDot X (blockMatVecMul E X) ∂P =
      (1 + ∫ a, bad.indicator nss a ∂P) * blockVecDot X (blockMatVecMul E X) := by
    rw [show (fun a => (1 + bad.indicator nss a) *
        blockVecDot X (blockMatVecMul E X)) =
        fun a => blockVecDot X (blockMatVecMul E X) +
          blockVecDot X (blockMatVecMul E X) * bad.indicator nss a from by
      funext a
      ring]
    rw [integral_add (integrable_const _) (hindint.const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    ring
  rw [hsplit] at hmono
  have hco : (1 + ∫ a, bad.indicator nss a ∂P) *
      blockVecDot X (blockMatVecMul E X) ≤
      (1 + euclideanEntryDefect K sK n) * blockVecDot X (blockMatVecMul E X) :=
    mul_le_mul_of_nonneg_right (by linarith only [hindmom]) (hquadE X)
  linarith only [hmono, hco]

/-! ## The scale threshold and the assembled comparison -/

/-- The Euclidean part of the printed entry threshold `n₁` (the printed argument): the
scale past which the annealed Euclidean envelope has defect at most `cEnt`.  It
is `s_K + log₃(M₂(K)/cEnt)`, i.e. the printed `4 log K_{Ψ_S} + A(d)` terms; the
remaining `2 log Π + (1-γ)^{-1}` terms of `n₁` belong to the adapted-cube
transfer and enter only as a threshold there as well. -/
@[expose]
def euclideanEntryThreshold (K cEnt : ℝ) (sK : ℤ) : ℤ :=
  sK + max 1 ⌈Real.logb 3 (sourceMomentTwo K / cEnt)⌉

theorem one_le_sourceMomentTwo (K : ℝ) : (1 : ℝ) ≤ sourceMomentTwo K := by
  rw [sourceMomentTwo]
  have hbar : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hlog : 0 ≤ Real.log (growthBar K) :=
    Real.log_nonneg (by linarith only [hbar])
  have hpow : (0 : ℝ) ≤ growthBar K ^ IndependentSums.natTriangular 2 :=
    pow_nonneg (by linarith only [hbar]) _
  have hcoef : (0 : ℝ) ≤ 2 * ((2 : ℕ) : ℝ) * (1 + Real.log (growthBar K)) := by
    push_cast
    linarith only [hlog]
  have hmul := mul_nonneg hcoef hpow
  linarith only [hmul]

/-- Past the threshold the entry defect is at most `cEnt`. -/
theorem euclideanEntryDefect_le {K cEnt : ℝ} (hcEnt : 0 < cEnt) {sK n : ℤ}
    (hn : euclideanEntryThreshold K cEnt sK ≤ n) :
    euclideanEntryDefect K sK n ≤ cEnt := by
  have hM1 : (1 : ℝ) ≤ sourceMomentTwo K := one_le_sourceMomentTwo K
  have hM0 : (0 : ℝ) < sourceMomentTwo K := lt_of_lt_of_le zero_lt_one hM1
  have hratio : (0 : ℝ) < sourceMomentTwo K / cEnt := div_pos hM0 hcEnt
  rw [euclideanEntryThreshold] at hn
  have hceil : ⌈Real.logb 3 (sourceMomentTwo K / cEnt)⌉ ≤ n - sK := by
    have h1 : ⌈Real.logb 3 (sourceMomentTwo K / cEnt)⌉ ≤
        max 1 ⌈Real.logb 3 (sourceMomentTwo K / cEnt)⌉ := le_max_right _ _
    omega
  have hlog : Real.logb 3 (sourceMomentTwo K / cEnt) ≤ ((n - sK : ℤ) : ℝ) := by
    refine le_trans (Int.le_ceil _) ?_
    exact_mod_cast hceil
  have hpow : sourceMomentTwo K / cEnt ≤ (3 : ℝ) ^ (((n - sK : ℤ) : ℝ)) := by
    rw [← Real.rpow_logb (b := 3) (by norm_num) (by norm_num) hratio]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  have hT : (0 : ℝ) < (3 : ℝ) ^ (n - sK) := zpow_pos (by norm_num) _
  have hpow' : sourceMomentTwo K / cEnt ≤ (3 : ℝ) ^ (n - sK) := by
    rwa [Real.rpow_intCast] at hpow
  have hMle : sourceMomentTwo K ≤ (3 : ℝ) ^ (n - sK) * cEnt :=
    (div_le_iff₀ hcEnt).mp hpow'
  have h := mul_le_mul_of_nonneg_right hMle (inv_nonneg.mpr hT.le)
  have hne : ((3 : ℝ) ^ (n - sK)) ≠ 0 := hT.ne'
  have hclean : (3 : ℝ) ^ (n - sK) * cEnt * ((3 : ℝ) ^ (n - sK))⁻¹ = cEnt := by
    field_simp
  rw [hclean] at h
  rw [euclideanEntryDefect]
  have hinv : (3 : ℝ) ^ (sK - n) = ((3 : ℝ) ^ (n - sK))⁻¹ := by
    rw [← zpow_neg]
    congr 1
    ring
  rw [hinv]
  exact h

end

end HCPolySupport.HighContrast.Quenched
