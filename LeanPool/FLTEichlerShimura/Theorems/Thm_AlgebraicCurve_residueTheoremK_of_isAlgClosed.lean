/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node AlgebraicCurve.residueTheoremK_of_isAlgClosed
(0b4c7479-cbcc-5c87-9c16-80c7c5d57ccc) by Claude (2026-09-05).

Proof based on Prove2Me submission 72e99470-19e3-5ea5-be87-5fc25dbfd308
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Mathlib.FieldTheory.RatFunc.Basic
public import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_IsCurveOver
public import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_LocalResidue
public import Mathlib.RingTheory.SimpleRing.Principal

import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import LeanPool.FLTEichlerShimura.Definitions.Defs_AlgebraicCurve_residueTheorem_sharedLibrary
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_residueTraceCompletionCommute
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Residue theorem over an algebraically closed base field

Theorem statement: `AlgebraicCurve.residueTheoremK_of_isAlgClosed`
(`0b4c7479-cbcc-5c87-9c16-80c7c5d57ccc`), by Claude, 2026-09-05.

Proof: submission `72e99470-19e3-5ea5-be87-5fc25dbfd308`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure,
subject to the following hypotheses. Geometric structure of $F/K$: every nonzero $\omega \in
\Omega[F⁄K]$ admits a divisor $D$ on the places of $F/K$ with $D(v) =
v.\mathrm{ordDifferential}\,\omega$ for all $v$ (`HasCanonicalDivisor`); for every place $w$ the
element $w.\mathrm{dCoord}$ spans $\Omega[F⁄K]$ over $F$ (`DCoordGenerates`); every $f \neq 0$ in
$F$ has a divisor of degree $0$ recording the orders $v.\mathrm{ord}\,f$ (`HasPrincipalDivisors`);
each residue field $\kappa(v)$ is finite-dimensional over $K$; $\Omega[F⁄K]$ is nontrivial, and
`IsCurveOver K F` holds, i.e. principal divisors exist, residue fields are finite over $K$, and
$\Omega[F⁄K]$ is free of rank one over $F$. Local residues: each place of $F/K$ carries a local
residue datum, and indeed `HasCanonicalLocalResidueKStar K F` provides a chosen family of canonical
local residue data — $K$-linear maps $\mathrm{res}_v : F \to \kappa(v)$ vanishing on the valuation
subring, sending $f$ with $\pi_v f$ integral to the residue class of $\pi_v f$, and annihilating
$(\pi_v^{n+1})^{-1}$ for $n \geq 1$. Presentation over a rational function field: $F$ is an algebra
over $\mathrm{RatFunc}\,K$, compatibly with $K$, integral, module-finite and separable over it,
while $\mathrm{RatFunc}\,K$ itself satisfies the same curve package over $K$ (`IsCurveOver`, finite
residue fields at all places, nontrivial $\Omega[\mathrm{RatFunc}\,K⁄K]$, and `DCoordGenerates` at
every place). The conclusion is `ResidueTheoremK K F`: for every family $R$ assigning to each place
$v$ of $F/K$ a canonical local residue datum, every nonzero $\omega \in \Omega[F⁄K]$ and every $f
\in F$, the Weil functional $\mathrm{weilOfKaehlerK}\,R\,\omega$ vanishes on the diagonal adèle of
$f$. Some hypotheses overlap: `IsCurveOver K F` already yields principal divisors and finiteness of
the residue fields, and `HasCanonicalLocalResidueKStar K F` already yields `HasLocalResidue K F`.

This is the residue theorem for the function field $F/K$ in its canonical $K$-valued (Tate) form:
the sum of the local residues of $f\,\omega$ over all places vanishes, expressed as the vanishing of
the associated adelic Weil functional on the diagonal copy of $F$. It is the input for the duality
step behind Riemann–Roch for function fields and for the construction of differentials with
prescribed orders, and is used by
[`AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed`]
(thm.html#AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed),
[`AlgebraicCurve.residueTheorem_of_isAlgClosed`]
(thm.html#AlgebraicCurve.residueTheorem_of_isAlgClosed)
and
[`AlgebraicCurve.exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`]
(thm.html#AlgebraicCurve.exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero);
its proof reduces the general case to the rational function field by the trace compatibility of
residues under the finite separable extension $F/\mathrm{RatFunc}\,K$.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean

*Attribution:* this file contains material adapted from third-party Apache-2.0 sources (one short
lemma (`IsLocalRing.maximalIdeal_le`): `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` —
© 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard). See ATTRIBUTION.md and NOTICE
in the source repository.

<!-- Generated by add_prove2me_provenance.py -->
-/

open AlgebraicCurve Place RationalFunctionField IntermediateField
  IsDedekindDomain HeightOneSpectrum IsLocalRing KaehlerDifferential ModularCurve
  ModularCurve.KwF4R1V391a Module Polynomial TensorProduct
  Valuation.IsRankOneDiscrete WithZero WithZeroMulInt

open scoped Valued

section privateSection

noncomputable section

namespace AlgebraicCurve

namespace Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 0] valuationSubringAlgebra

section Assembly

variable (v : Place K F)

theorem sum_ramificationIndex_mul_inertiaDeg [HasPrincipalDivisors K F'] :
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  have hkey := sum_ramificationIdx'_mul_inertiaDeg'_integralClosureAt (F' := F') v
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v (Place.mem_fiber.mp hw)).asIdeal) ?_ ?_ ?_ ?_
  · intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v (Place.mem_fiber.mp hw)).isPrime,
      fiberCenter_liesOver (Place.mem_fiber.mp hw)⟩
  · intro w hw w' hw' h
    exact eq_of_fiberCenter_eq (Place.mem_fiber.mp hw) (Place.mem_fiber.mp hw')
      (HeightOneSpectrum.ext h)
  · intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)] at hP
    obtain ⟨hP1, hP2⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro h
      apply maximalIdeal_ne_bot v
      have h2 := hP2.over
      rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
        (algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨placeOfPrime ⟨P, hP1, hPne⟩,
      Place.mem_fiber.mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  · intro w hw
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter _ (Place.mem_fiber.mp hw),
      inertiaDeg_eq_inertiaDeg_fiberCenter (Place.mem_fiber.mp hw)]

end Assembly
end Place
end AlgebraicCurve
end
section

noncomputable section

namespace AlgebraicCurve
namespace Place

section IntegerComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal
    {x : (W.restrict F).adicCompletionIntegers}
    (hx : x ∈ maximalIdeal (W.restrict F).adicCompletionIntegers) :
    kwFfgcAdicCompletionComapIntegers F W x ∈ maximalIdeal W.adicCompletionIntegers := by
  have hrpos := W.ramificationIndex_pos (F := F)
  rw [show maximalIdeal (W.restrict F).adicCompletionIntegers
      = (W.restrict F).heightOneSpectrum.completionIdeal F from rfl,
    HeightOneSpectrum.mem_completionIdeal_iff] at hx
  rw [show maximalIdeal W.adicCompletionIntegers
      = W.heightOneSpectrum.completionIdeal F' from rfl,
    HeightOneSpectrum.mem_completionIdeal_iff, kw_ffgc_adicCompletionComapIntegers_coe,
    kw_ffgc_valued_adicCompletionComap]
  calc Valued.v (x : (W.restrict F).adicCompletion) ^ W.ramificationIndex F
      < 1 ^ W.ramificationIndex F := pow_lt_pow_left₀ hx (zero_le) hrpos.ne'
    _ = 1 := one_pow _

scoped instance kw_ffgc_isLocalHom_adicCompletionComapIntegers :
    IsLocalHom (kwFfgcAdicCompletionComapIntegers F W) where
  map_nonunit x hx := by
    by_contra hnu
    exact (IsLocalRing.notMem_maximalIdeal.mpr hx)
      (kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal F W
        ((IsLocalRing.mem_maximalIdeal x).mpr hnu))

end IntegerComap
end Place
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve
namespace Place

section CompletionAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

scoped instance kw_ffgc_isIntegrallyClosed_adicCompletionIntegers :
    IsIntegrallyClosed (W.restrict F).adicCompletionIntegers :=
  Valuation.Integers.isIntegrallyClosed
    (HeightOneSpectrum.adicCompletionIntegers.integers
      (K := F) (v := (W.restrict F).heightOneSpectrum))

end CompletionAlgebra
section SpectralSetup

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

theorem kw_ffgc_norm_adicCompletion_eq (x : V.adicCompletion) :
    letI := kwFfgcRankOneAdicCompletion V
    ‖x‖ = (WithZeroMulInt.toNNReal (two_ne_zero) (Valued.v x) : ℝ) := by
  let := kwFfgcRankOneAdicCompletion V
  have h := valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (V.heightOneSpectrum.valuedAdicCompletion_surjective F) x
  simp only [Valued.toNormedField.norm_def, Valuation.RankOne.hom]
  rw [← h]; rfl

end SpectralSetup
section AbsoluteValue

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_absoluteValue_extends (c : (W.restrict F).adicCompletion) :
    letI := kwFfgcRankOneAdicCompletion (W.restrict F)
    kwFfgcAbsoluteValue F W
      (algebraMap (W.restrict F).adicCompletion W.adicCompletion c) = ‖c‖ := by
  let := kwFfgcRankOneAdicCompletion (W.restrict F)
  let := kwFfgcRankOneAdicCompletion W
  have hr : (0 : ℝ) < (W.ramificationIndex F : ℝ) :=
    Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F))
  change ‖algebraMap (W.restrict F).adicCompletion W.adicCompletion c‖
      ^ ((W.ramificationIndex F : ℝ))⁻¹ = ‖c‖
  rw [kw_ffgc_norm_adicCompletion_eq W, kw_ffgc_norm_adicCompletion_eq (W.restrict F),
    kw_ffgc_algebraMap_adicCompletionComap_eq, kw_ffgc_valued_adicCompletionComap,
    map_pow, NNReal.coe_pow, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _),
    mul_inv_cancel₀ hr.ne', Real.rpow_one]

end AbsoluteValue
section IntegralClosure

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic
    [Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion]
    (x : W.adicCompletionIntegers) :
    _root_.IsIntegral (W.restrict F).adicCompletionIntegers x := by
  let := kwFfgcRankOneAdicCompletion (W.restrict F)
  let := kwFfgcRankOneAdicCompletion W
  let : NontriviallyNormedField (W.restrict F).adicCompletion :=
    Valued.toNontriviallyNormedField (W.restrict F).adicCompletion ℤᵐ⁰
  have : IsUltrametricDist (W.restrict F).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  have hr : (0 : ℝ) < ((W.ramificationIndex F : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F)))
  have hxn : ‖(x : W.adicCompletion)‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr x.2
  have hsn : spectralNorm (W.restrict F).adicCompletion W.adicCompletion
        (x : W.adicCompletion)
      = ‖(x : W.adicCompletion)‖ ^ ((W.ramificationIndex F : ℝ))⁻¹ :=
    (spectralNorm_unique_field_norm_ext (f := kwFfgcAbsoluteValue F W)
      (kw_ffgc_absoluteValue_extends F W) (x : W.adicCompletion)).symm
  have hspec : spectralValue (minpoly (W.restrict F).adicCompletion
      (x : W.adicCompletion)) ≤ 1 := by
    change spectralNorm (W.restrict F).adicCompletion W.adicCompletion
      (x : W.adicCompletion) ≤ 1
    rw [hsn]; exact Real.rpow_le_one (norm_nonneg _) hxn hr.le
  have hmon : (minpoly (W.restrict F).adicCompletion (x : W.adicCompletion)).Monic :=
    minpoly.monic (Algebra.IsAlgebraic.isAlgebraic
      (R := (W.restrict F).adicCompletion) (x : W.adicCompletion)).isIntegral
  have hlift : minpoly (W.restrict F).adicCompletion (x : W.adicCompletion)
      ∈ Polynomial.lifts (algebraMap (W.restrict F).adicCompletionIntegers
          (W.restrict F).adicCompletion) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, ?_⟩, rfl⟩
    exact (Valued.toNormedField.norm_le_one_iff).mp
      ((spectralValue_le_one_iff hmon).mp hspec n)
  obtain ⟨P, hP, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hxintW : _root_.IsIntegral (W.restrict F).adicCompletionIntegers (x : W.adicCompletion) := by
    refine ⟨P, hPmon, ?_⟩
    rw [← Polynomial.aeval_def,
      ← Polynomial.aeval_map_algebraMap (W.restrict F).adicCompletion, hP, minpoly.aeval]
  exact (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom (W.restrict F).adicCompletionIntegers
      W.adicCompletionIntegers W.adicCompletion)
    Subtype.val_injective).mp hxintW

theorem kw_ffgc_isIntegralClosure_adicCompletionIntegers
    [Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion] :
    IsIntegralClosure W.adicCompletionIntegers (W.restrict F).adicCompletionIntegers
      W.adicCompletion where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hxW : _root_.IsIntegral W.adicCompletionIntegers x := hx.tower_top
      have : IsIntegrallyClosed W.adicCompletionIntegers :=
        Valuation.Integers.isIntegrallyClosed
          (HeightOneSpectrum.adicCompletionIntegers.integers
            (K := F') (v := W.heightOneSpectrum))
      exact IsIntegrallyClosed.isIntegral_iff.mp hxW
    · rintro ⟨y, rfl⟩
      exact (kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic F W y).map
        (IsScalarTower.toAlgHom (W.restrict F).adicCompletionIntegers
          W.adicCompletionIntegers W.adicCompletion)

end IntegralClosure
end Place
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve
namespace Place

section CompletionTrace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_completionTraceF'_apply (g : F') :
    kwFfgcCompletionTraceF' F W g
      = Algebra.trace (W.restrict F).adicCompletion W.adicCompletion
          (algebraMap F' W.adicCompletion g) := rfl

end CompletionTrace
section ResidueCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

def kw_ffgc_residueFieldEquivCompletionResidueField :
    V.ResidueField ≃+* IsLocalRing.ResidueField V.adicCompletionIntegers :=
  ResidueFieldEquivCompletionResidueField F V.heightOneSpectrum

end ResidueCompletion
end Place
end AlgebraicCurve
end
noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

private theorem subsingleton_canonicalLocalResidueDataK_of_surj
    (hsurj : Function.Surjective (algebraMap K v.ResidueField)) :
    Subsingleton v.CanonicalLocalResidueDataK := by
  constructor
  intro R₁ R₂
  have hres : R₁.res = R₂.res := by
    ext f
    obtain ⟨n, hn⟩ := v.exists_mem_poleSubmodule f
    exact v.canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj hsurj R₁ R₂ n hn
  obtain ⟨⟨r₁, h₁a, h₁b⟩, h₁c⟩ := R₁
  obtain ⟨⟨r₂, h₂a, h₂b⟩, h₂c⟩ := R₂
  congr 2

end Place
end AlgebraicCurve
end
noncomputable section

namespace AlgebraicCurve

section FiberReindex

variable {K E F : Type*} [Field K] [Field E] [Field F]
variable [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K F]

variable {M : Type*} [AddCommMonoid M]

theorem finsum_place_eq_finsum_fiber_sum (g : Place K F → M)
    (hg : (Function.support g).Finite) :
    ∑ᶠ w, g w = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F, g w := by
  classical
  set S := hg.toFinset with hS
  set T := S.image (fun w => w.restrict E) with hT
  rw [finsum_eq_finsetSum_of_support_subset g
    (s := S) (fun w hw => (hS ▸ hg.mem_toFinset.mpr hw))]
  have hsup : Function.support (fun v : Place K E => ∑ w ∈ v.fiber F, g w) ⊆ ↑T := by
    intro v hv
    simp only [Function.mem_support] at hv
    obtain ⟨w, hwfib, hwne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    exact Finset.mem_coe.mpr (hT ▸ Finset.mem_image.mpr
      ⟨w, hS ▸ hg.mem_toFinset.mpr hwne, Place.mem_fiber.mp hwfib⟩)
  rw [finsum_eq_finsetSum_of_support_subset _ hsup]
  have hfib : ∀ v ∈ T, ∑ w ∈ v.fiber F, g w
      = ∑ w ∈ S with w.restrict E = v, g w := by
    intro v _
    refine (Finset.sum_subset ?_ ?_).symm
    · intro w hw
      exact Place.mem_fiber.mpr (Finset.mem_filter.mp hw).2
    · intro w hwfib hwfilt
      by_contra hgw
      exact hwfilt (Finset.mem_filter.mpr
        ⟨hS ▸ hg.mem_toFinset.mpr hgw, Place.mem_fiber.mp hwfib⟩)
  rw [Finset.sum_congr rfl hfib]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun w hw => hT ▸ Finset.mem_image.mpr ⟨w, hw, rfl⟩) g).symm

end FiberReindex
end AlgebraicCurve
end
noncomputable section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

@[scoped simp]
private theorem mem_regularSubmodule (w : Place K F) (ωF : Ω[F⁄K])
    (f : F) :
    f ∈ w.regularSubmodule ωF ↔ f * w.differentialCoeff ωF ∈ w.toValuationSubring := Iff.rfl

end Place
end AlgebraicCurve
end
noncomputable section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private def regularPoleSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (n : ℕ) :
    Submodule K F :=
  (w.poleSubmodule n).comap (LinearMap.mulRight K (w.differentialCoeff ωF))

@[scoped simp]
private theorem mem_regularPoleSubmodule (w : Place K F) (ωF : Ω[F⁄K])
    (n : ℕ) (f : F) :
    f ∈ w.regularPoleSubmodule ωF n
      ↔ w.uniformizer ^ n * (f * w.differentialCoeff ωF) ∈ w.toValuationSubring := Iff.rfl

theorem regularPoleSubmodule_zero (w : Place K F) (ωF : Ω[F⁄K]) :
    w.regularPoleSubmodule ωF 0 = w.regularSubmodule ωF := by
  ext f
  simp only [mem_regularPoleSubmodule, pow_zero, one_mul, mem_regularSubmodule]

private theorem regularPoleSubmodule_mono (w : Place K F) (ωF : Ω[F⁄K])
    :
    Monotone (w.regularPoleSubmodule ωF) :=
  fun _ _ hmn => Submodule.comap_mono (w.poleSubmodule_mono hmn)

private theorem iSup_regularPoleSubmodule_eq_top (w : Place K F)
    (ωF : Ω[F⁄K]) :
    ⨆ n, w.regularPoleSubmodule ωF n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hmem : f * w.differentialCoeff ωF ∈ ⨆ n, w.poleSubmodule n :=
    w.iSup_poleSubmodule_eq_top ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _
    (Monotone.directed_le w.poleSubmodule_mono)).mp hmem
  exact Submodule.mem_iSup_of_mem n hn

private theorem exists_mem_regularPoleSubmodule (w : Place K F)
    (ωF : Ω[F⁄K]) (f : F) :
    ∃ n, f ∈ w.regularPoleSubmodule ωF n := by
  have h : f ∈ ⨆ n, w.regularPoleSubmodule ωF n :=
    (w.iSup_regularPoleSubmodule_eq_top ωF) ▸ Submodule.mem_top
  exact (Submodule.mem_iSup_of_directed _
    (Monotone.directed_le (w.regularPoleSubmodule_mono ωF))).mp h

end Place
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve

section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

def FiberKaehlerCotraceResidueIdentity : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (f : F),
    ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w
      = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F f)) v

end CorrectedCarrier
end AlgebraicCurve
end
noncomputable section

namespace AlgebraicCurve

section KaehlerCotrace

variable (K E F : Type*) [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

variable {K E F}

theorem kaehlerCotrace_D (e : E) :
    kaehlerCotrace K E F (KaehlerDifferential.D K E e)
      = KaehlerDifferential.D K F (algebraMap E F e) :=
  KaehlerDifferential.map_D K K E F e

theorem kaehlerCotrace_smul_algebraMap (e : E) (ωE : Ω[E⁄K]) :
    kaehlerCotrace K E F (e • ωE) = (algebraMap E F e) • kaehlerCotrace K E F ωE := by
  rw [LinearMap.map_smul, algebra_compatible_smul F e]

end KaehlerCotrace
end AlgebraicCurve
end
section

namespace AlgebraicCurve

section SeparatingWitness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F]
    [IsScalarTower K E F]

theorem kaehlerCotrace_dCoord_ne_zero_of_exists
    (v : Place K E) [v.DCoordGenerates]
    {ωE₀ : Ω[E⁄K]} (h : kaehlerCotrace K E F ωE₀ ≠ 0) :
    kaehlerCotrace K E F v.dCoord ≠ 0 := by
  intro hdc
  apply h
  rw [← v.differentialCoeff_smul_dCoord ωE₀, kaehlerCotrace_smul_algebraMap, hdc, smul_zero]

theorem exists_kaehlerCotrace_ne_zero_of_D_algebraMap_ne_zero
    {e : E} (he : KaehlerDifferential.D K F (algebraMap E F e) ≠ 0) :
    ∃ ωE : Ω[E⁄K], kaehlerCotrace K E F ωE ≠ 0 :=
  ⟨KaehlerDifferential.D K E e, by rw [kaehlerCotrace_D]; exact he⟩

end SeparatingWitness
end AlgebraicCurve
end
section

namespace AlgebraicCurve

section CotraceInjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

theorem kaehlerCotrace_injective_iff_dCoord_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]] :
    Function.Injective (kaehlerCotrace K E F) ↔ kaehlerCotrace K E F v.dCoord ≠ 0 := by
  constructor
  · intro hinj h0
    exact v.dCoord_ne_zero (hinj (h0.trans (_root_.map_zero _).symm))
  · intro hne ωE ωE' heq
    obtain ⟨e, rfl⟩ := v.exists_eq_smul_dCoord ωE
    obtain ⟨e', rfl⟩ := v.exists_eq_smul_dCoord ωE'
    rw [kaehlerCotrace_smul_algebraMap, kaehlerCotrace_smul_algebraMap] at heq
    have hee' : algebraMap E F e = algebraMap E F e' :=
      smul_left_injective F hne heq
    rw [(algebraMap E F).injective hee']

theorem kaehlerCotrace_injective_of_exists_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    {ωE₀ : Ω[E⁄K]} (h : kaehlerCotrace K E F ωE₀ ≠ 0) :
    Function.Injective (kaehlerCotrace K E F) :=
  (kaehlerCotrace_injective_iff_dCoord_ne_zero v).mpr
    (kaehlerCotrace_dCoord_ne_zero_of_exists v h)

theorem kaehlerCotrace_injective_of_D_algebraMap_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    {e : E} (he : KaehlerDifferential.D K F (algebraMap E F e) ≠ 0) :
    Function.Injective (kaehlerCotrace K E F) :=
  let ⟨_, hωE⟩ := exists_kaehlerCotrace_ne_zero_of_D_algebraMap_ne_zero he
  kaehlerCotrace_injective_of_exists_ne_zero v hωE

end CotraceInjective
end AlgebraicCurve
end
section

namespace AlgebraicCurve

section CotraceDX

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem kaehlerCotrace_dX_eq :
    kaehlerCotrace K (RatFunc K) F (dX K)
      = KaehlerDifferential.D K F (algebraMap (RatFunc K) F RatFunc.X) :=
  kaehlerCotrace_D RatFunc.X

end CotraceDX
section SeparatingCarrier

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
    [Algebra (RatFunc K) F]

def IsSeparatingTranscendental : Prop :=
  KaehlerDifferential.D K F (algebraMap (RatFunc K) F RatFunc.X) ≠ 0

end SeparatingCarrier
section SeparatingEngine

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem kaehlerCotrace_dX_ne_zero_of_isSeparatingTranscendental
    (hsep : IsSeparatingTranscendental K F) :
    kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 := by
  rw [kaehlerCotrace_dX_eq]; exact hsep

theorem isSeparatingTranscendental_iff_kaehlerCotrace_dX_ne_zero :
    IsSeparatingTranscendental K F ↔ kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 := by
  rw [IsSeparatingTranscendental, kaehlerCotrace_dX_eq]

end SeparatingEngine
end AlgebraicCurve
end
section

namespace AlgebraicCurve

section SepIffInjective

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem isSeparatingTranscendental_iff_kaehlerCotrace_injective
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] :
    IsSeparatingTranscendental K F ↔ Function.Injective (kaehlerCotrace K (RatFunc K) F) := by
  constructor
  · exact fun hsep => kaehlerCotrace_injective_of_D_algebraMap_ne_zero v hsep
  · intro hinj
    rw [isSeparatingTranscendental_iff_kaehlerCotrace_dX_ne_zero]
    exact fun h0 => dX_ne_zero K (hinj (h0.trans (_root_.map_zero _).symm))

end SepIffInjective
section MapBaseChangeSurj

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F]
    [IsScalarTower K E F]

theorem surjective_mapBaseChange_of_formallyUnramified [Algebra.FormallyUnramified E F] :
    Function.Surjective (KaehlerDifferential.mapBaseChange K E F) := by
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange]
  exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)

end MapBaseChangeSurj
section CotraceNeZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F]
    [IsScalarTower K E F]

theorem exists_kaehlerCotrace_ne_zero_of_formallyUnramified
    [Algebra.FormallyUnramified E F] [Nontrivial Ω[F⁄K]] :
    ∃ ωE : Ω[E⁄K], kaehlerCotrace K E F ωE ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hmap0 : ∀ t, KaehlerDifferential.mapBaseChange K E F t = 0 := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul f ωE =>
        rw [KaehlerDifferential.mapBaseChange_tmul]
        change f • kaehlerCotrace K E F ωE = 0
        rw [h ωE, smul_zero]
    | add a b ha hb => rw [map_add, ha, hb, add_zero]
  obtain ⟨ωF, hωF⟩ := exists_ne (0 : Ω[F⁄K])
  obtain ⟨t, ht⟩ := surjective_mapBaseChange_of_formallyUnramified (K := K) (E := E) (F := F) ωF
  exact hωF (ht ▸ hmap0 t)

end CotraceNeZero
section CotraceInjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F]
    [IsScalarTower K E F]

theorem kaehlerCotrace_injective_of_formallyUnramified
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    [Algebra.FormallyUnramified E F] [Nontrivial Ω[F⁄K]] :
    Function.Injective (kaehlerCotrace K E F) := by
  obtain ⟨ωE₀, hωE₀⟩ :=
    exists_kaehlerCotrace_ne_zero_of_formallyUnramified (K := K) (E := E) (F := F)
  exact kaehlerCotrace_injective_of_exists_ne_zero v hωE₀

end CotraceInjective
section SepDischarge

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem isSeparatingTranscendental_of_formallyUnramified
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.FormallyUnramified (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    IsSeparatingTranscendental K F :=
  (isSeparatingTranscendental_iff_kaehlerCotrace_injective K F v).mpr
    (kaehlerCotrace_injective_of_formallyUnramified v)

theorem isSeparatingTranscendental_of_isSeparable
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.IsSeparable (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    IsSeparatingTranscendental K F :=
  haveI := Algebra.FormallyUnramified.of_isSeparable (RatFunc K) F
  isSeparatingTranscendental_of_formallyUnramified K F v

end SepDischarge
end AlgebraicCurve
end
section

namespace AlgebraicCurve

section CotraceDXSeparable

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

theorem kaehlerCotrace_dX_ne_zero_of_isSeparable
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.IsSeparable (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 :=
  kaehlerCotrace_dX_ne_zero_of_isSeparatingTranscendental K F
    (isSeparatingTranscendental_of_isSeparable K F v)

end CotraceDXSeparable
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve

section CurrencyBridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F]
    [IsScalarTower K E F]

theorem kaehlerPullback_eq_kaehlerCotrace (ωE : Ω[E⁄K]) :
    kaehlerPullback K F E ωE = kaehlerCotrace K E F ωE := rfl

end CurrencyBridge
section NamedRows

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E] [Algebra E F]
    [IsScalarTower K E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]
variable [Algebra.IsIntegral E F]

def CotraceResidueIdentityOnFiberLocalized : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (p : F),
    (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
      p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
      p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
    ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F p) w
      = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F p)) v

def CotraceFiberLocalizedPolarApprox : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (w : Place K F) (_ : w ∈ v.fiber F) (n : ℕ) (f : F)
    (_ : f ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) (n + 1)),
    ∃ p : F,
      f - p ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) n ∧
      ∀ w' ∈ v.fiber F, w' ≠ w → p ∈ w'.regularSubmodule (kaehlerPullback K F E ωE)

end NamedRows
end AlgebraicCurve
end
section S18AliasT2
open scoped AlgebraicCurve in
theorem AlgebraicCurve.p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K) := by
  classical
  exact
    AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed K
end S18AliasT2

noncomputable section

namespace AlgebraicCurve

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

theorem residueTheoremK_of_cotraceResidueIdentityK
    [HasPrincipalDivisors K E]
    (hE : ResidueTheoremK K E)
    {ωE₀ : Ω[E⁄K]} (hωE₀ : ωE₀ ≠ 0) (hgen : kaehlerPullback K F E ωE₀ ≠ 0)
    (hIdentK : FiberKaehlerCotraceResidueIdentityK K F E) :
    ResidueTheoremK K F := by
  intro RfamF _ ωF hωF f
  have : Nontrivial Ω[F⁄K] := ⟨ωF, 0, hωF⟩
  rcases isEmpty_or_nonempty (Place K F) with hempty | hne
  · rw [weilOfKaehlerK_apply]
    exact finsum_eq_zero_of_forall_eq_zero fun w => (hempty.false w).elim
  obtain ⟨w₀⟩ := hne
  obtain ⟨RfamE, hident⟩ := hIdentK RfamF hωE₀ hgen
  have hcoeff : w₀.differentialCoeff (kaehlerPullback K F E ωE₀) ≠ 0 :=
    w₀.differentialCoeff_ne_zero hgen
  have hωF_eq : ωF = (w₀.differentialCoeff ωF
      * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
        • kaehlerPullback K F E ωE₀ := by
    have key : (w₀.differentialCoeff ωF
        * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
          • kaehlerPullback K F E ωE₀ = ωF := by
      calc (w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
              • kaehlerPullback K F E ωE₀
          = (w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
                • (w₀.differentialCoeff (kaehlerPullback K F E ωE₀) • w₀.dCoord) := by
            rw [w₀.differentialCoeff_smul_dCoord]
        _ = ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
                * w₀.differentialCoeff (kaehlerPullback K F E ωE₀)) • w₀.dCoord := by
            rw [smul_smul]
        _ = w₀.differentialCoeff ωF • w₀.dCoord := by
            rw [mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
        _ = ωF := w₀.differentialCoeff_smul_dCoord ωF
    exact key.symm
  have hterm : ∀ w : Place K F,
      kaehlerResidueTermKFam RfamF ωF (diagonalHom K F f) w
        = kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
            (diagonalHom K F ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w := by
    intro w
    conv_lhs => rw [hωF_eq]
    exact kaehlerResidueTermKFam_smul_diagonal RfamF _ (kaehlerPullback K F E ωE₀) f w
  have hsup : (Function.support (kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
      (diagonalHom K F ((w₀.differentialCoeff ωF
        * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)))).Finite :=
    kaehlerResidueTermKFam_support_finite_of_adeleSpace RfamF hgen
      (diagonal_mem_adeleSpace _)
  calc weilOfKaehlerK RfamF hωF ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = ∑ᶠ w : Place K F, kaehlerResidueTermKFam RfamF ωF (diagonalHom K F f) w :=
        weilOfKaehlerK_apply RfamF hωF _
    _ = ∑ᶠ w : Place K F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
          (diagonalHom K F ((w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w :=
        finsum_congr hterm
    _ = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F,
          kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
            (diagonalHom K F ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w :=
        finsum_place_eq_finsum_fiber_sum (E := E) _ hsup
    _ = ∑ᶠ v : Place K E, kaehlerResidueTermKFam RfamE ωE₀
          (diagonalHom K E (Algebra.trace E F ((w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f))) v :=
        finsum_congr fun v => hident v _
    _ = 0 := by
        have h0 := hE RfamE hωE₀ (Algebra.trace E F ((w₀.differentialCoeff ωF
          * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f))
        rw [weilOfKaehlerK_apply] at h0
        exact h0

end Engine
section RatFuncFloorSupply

variable {K F : Type*} [Field K] [IsAlgClosed K]
variable [Field F] [Algebra K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]

theorem residueTheoremK_of_cotraceResidueIdentityK_ratFunc_isAlgClosed
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hIdentK : FiberKaehlerCotraceResidueIdentityK K F (RatFunc K)) :
    ResidueTheoremK K F := by
  classical
  exact
    residueTheoremK_of_cotraceResidueIdentityK
      (p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed K)
      (dX_ne_zero K) hgen hIdentK

end RatFuncFloorSupply
end AlgebraicCurve
end
noncomputable section

namespace Cotpk43T3

local notation "Qbar" => AlgebraicClosure ℚ

section DVRSandwich

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem cotpk43_t3_toValuationSubring_eq_of_dedekind_le
    (O : ValuationSubring F) (hO : IsDedekindDomain O)
    (v : Place k F) (hle : O ≤ v.toValuationSubring) :
    v.toValuationSubring = O := by
  have := hO
  have hSP : O.ofPrime (O.idealOfLE v.toValuationSubring hle) = v.toValuationSubring :=
    ValuationSubring.ofPrime_idealOfLE O v.toValuationSubring hle
  rcases eq_or_ne (O.idealOfLE v.toValuationSubring hle) ⊥ with hP | hP
  · exfalso
    apply v.ne_top'
    have h2 : O.ofPrime ⊥ ≤ O.ofPrime (O.idealOfLE v.toValuationSubring hle) :=
      ValuationSubring.ofPrime_le_of_le (h := hP.le)
    rw [ValuationSubring.ofPrime_bot] at h2
    exact top_le_iff.mp (le_trans h2 hSP.le)
  · have hPmax : (O.idealOfLE v.toValuationSubring hle).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hP
    have hPeq : O.idealOfLE v.toValuationSubring hle = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal hPmax
    have h3 : O.ofPrime (O.idealOfLE v.toValuationSubring hle)
        = O.ofPrime (IsLocalRing.maximalIdeal O) :=
      le_antisymm (ValuationSubring.ofPrime_le_of_le (h := hPeq.ge))
        (ValuationSubring.ofPrime_le_of_le (h := hPeq.le))
    rw [ValuationSubring.ofPrime_top] at h3
    rw [hSP] at h3
    exact h3

theorem cotpk43_t3_place_eq_of_dedekind_le
    (O : ValuationSubring F) (hO : IsDedekindDomain O)
    (v w : Place k F) (hv : O ≤ v.toValuationSubring) (hw : O ≤ w.toValuationSubring) :
    v = w :=
  Place.ext ((cotpk43_t3_toValuationSubring_eq_of_dedekind_le O hO v hv).trans
    (cotpk43_t3_toValuationSubring_eq_of_dedekind_le O hO w hw).symm)

theorem cotpk43_t3_place_eq_of_toValuationSubring_le
    (v w : Place k F) (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w :=
  cotpk43_t3_place_eq_of_dedekind_le v.toValuationSubring inferInstance v w le_rfl h

end DVRSandwich
end Cotpk43T3
end

noncomputable section

namespace ModularCurve

section Toolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem gf24a9r_ord_neg (v : Place K F) (g : F) : v.ord (-g) = v.ord g := by
  simp only [Place.ord, Valuation.map_neg]

theorem gf24a9r_ord_pow (v : Place K F) (g : F) (m : ℕ) :
    v.ord (g ^ m) = (m : ℤ) * v.ord g := by
  rw [show (g ^ m : F) = g ^ (m : ℤ) from (zpow_natCast g m).symm, v.ord_zpow]

theorem gf24a9r_one_add_ne_zero_of_ord_pos (v : Place K F) {g : F}
    (h : 0 < v.ord g) : (1 : F) + g ≠ 0 := by
  intro hcon
  have hg1 : g = -(1 : F) := by
    rw [add_comm] at hcon
    exact eq_neg_of_add_eq_zero_left hcon
  have h0 : v.ord g = 0 := by rw [hg1, gf24a9r_ord_neg, v.ord_one]
  omega

theorem gf24a9r_ord_one_add_of_ord_pos (v : Place K F) {g : F} (hg : g ≠ 0)
    (h : 0 < v.ord g) : v.ord (1 + g) = 0 := by
  have hmin := v.ord_add_eq_min (f := (1 : F)) one_ne_zero hg
    (by rw [v.ord_one]; omega)
  rw [v.ord_one] at hmin
  rw [hmin, min_eq_left h.le]

theorem gf24a9r_ord_one_add_of_ord_neg (v : Place K F) {g : F} (hg : g ≠ 0)
    (h : v.ord g < 0) : v.ord (1 + g) = v.ord g := by
  have hmin := v.ord_add_eq_min (f := (1 : F)) one_ne_zero hg
    (by rw [v.ord_one]; omega)
  rw [v.ord_one] at hmin
  rw [hmin, min_eq_right h.le]

theorem gf24a9r_exists_ord_pos_ord_neg {w₁ w₂ : Place K F} (h : w₁ ≠ w₂) :
    ∃ u : F, u ≠ 0 ∧ 0 < w₁.ord u ∧ w₂.ord u < 0 := by
  have h12 : ¬(w₁.toValuationSubring ≤ w₂.toValuationSubring) := fun hle =>
    h (Cotpk43T3.cotpk43_t3_place_eq_of_toValuationSubring_le w₁ w₂ hle)
  have h21 : ¬(w₂.toValuationSubring ≤ w₁.toValuationSubring) := fun hle =>
    h.symm (Cotpk43T3.cotpk43_t3_place_eq_of_toValuationSubring_le w₂ w₁ hle)
  obtain ⟨x, hx1, hx2⟩ := IsConcreteLE.not_le_iff_exists.mp h12
  obtain ⟨y, hy2, hy1⟩ := IsConcreteLE.not_le_iff_exists.mp h21
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)
  have hy0 : y ≠ 0 := by rintro rfl; exact hy1 (zero_mem _)
  have hx1o : 0 ≤ w₁.ord x := w₁.ord_nonneg_of_mem hx1
  have hy2o : 0 ≤ w₂.ord y := w₂.ord_nonneg_of_mem hy2
  have hx2o : w₂.ord x < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hx2 (w₂.mem_of_ord_nonneg hx0 hcon)
  have hy1o : w₁.ord y < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hy1 (w₁.mem_of_ord_nonneg hy0 hcon)
  refine ⟨x * y⁻¹, mul_ne_zero hx0 (inv_ne_zero hy0), ?_, ?_⟩
  · rw [w₁.ord_mul hx0 (inv_ne_zero hy0), w₁.ord_inv]
    omega
  · rw [w₂.ord_mul hx0 (inv_ne_zero hy0), w₂.ord_inv]
    omega

theorem gf24a9r_exists_separator (w : Place K F) (S : Finset (Place K F)) (hw : w ∉ S) :
    ∃ u : F, u ≠ 0 ∧ 0 < w.ord u ∧ ∀ w' ∈ S, w'.ord u < 0 := by
  classical
  revert hw
  induction S using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨g, hg0, hgord⟩ := w.exists_ord_pos
    exact ⟨g, hg0, hgord, fun w' hw' => absurd hw' (Finset.notMem_empty w')⟩
  | @insert a S' ha ih =>
    intro hw
    have hwa : w ≠ a := fun hcon => hw (hcon ▸ Finset.mem_insert_self a S')
    have hwS' : w ∉ S' := fun hcon => hw (Finset.mem_insert_of_mem hcon)
    obtain ⟨y, hy0, hyw, hyS'⟩ := ih hwS'
    obtain ⟨z, hz0, hzw, hza⟩ := gf24a9r_exists_ord_pos_ord_neg hwa
    rcases lt_trichotomy (a.ord y) 0 with hneg | hzero | hpos
    · refine ⟨y, hy0, hyw, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.mp hw' with rfl | hw'S'
      · exact hneg
      · exact hyS' w' hw'S'
    · obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ S', w'.ord z < (r : ℤ) := by
        refine ⟨S'.sup (fun w' => (w'.ord z).toNat) + 1, Nat.le_add_left 1 _,
          fun w' hw' => ?_⟩
        have hle : (w'.ord z).toNat ≤ S'.sup (fun p => (p.ord z).toNat) :=
          Finset.le_sup (f := fun p => (p.ord z).toNat) hw'
        have h1 : w'.ord z ≤ ((w'.ord z).toNat : ℤ) := Int.self_le_toNat _
        have h2 : ((w'.ord z).toNat : ℤ)
            ≤ ((S'.sup (fun p => (p.ord z).toNat) : ℕ) : ℤ) := by exact_mod_cast hle
        omega
      have hyr0 : y ^ r ≠ 0 := pow_ne_zero r hy0
      have hordeq : ∀ p : Place K F, p.ord (y ^ r * z) = (r : ℤ) * p.ord y + p.ord z :=
        fun p => by rw [p.ord_mul hyr0 hz0, gf24a9r_ord_pow]
      refine ⟨y ^ r * z, mul_ne_zero hyr0 hz0, ?_, fun w' hw' => ?_⟩
      · rw [hordeq w]
        have hnn : 0 ≤ (r : ℤ) * w.ord y := mul_nonneg (by omega) hyw.le
        linarith
      · rcases Finset.mem_insert.mp hw' with rfl | hw'S'
        · rw [hordeq w', hzero, mul_zero, zero_add]
          exact hza
        · rw [hordeq w']
          have h1 : w'.ord y ≤ -1 := by have := hyS' w' hw'S'; omega
          have h2 : (r : ℤ) * w'.ord y ≤ (r : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left h1 (by omega)
          have h3 := hrB w' hw'S'
          linarith
    · obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ S', w'.ord z < (r : ℤ) := by
        refine ⟨S'.sup (fun w' => (w'.ord z).toNat) + 1, Nat.le_add_left 1 _,
          fun w' hw' => ?_⟩
        have hle : (w'.ord z).toNat ≤ S'.sup (fun p => (p.ord z).toNat) :=
          Finset.le_sup (f := fun p => (p.ord z).toNat) hw'
        have h1 : w'.ord z ≤ ((w'.ord z).toNat : ℤ) := Int.self_le_toNat _
        have h2 : ((w'.ord z).toNat : ℤ)
            ≤ ((S'.sup (fun p => (p.ord z).toNat) : ℕ) : ℤ) := by exact_mod_cast hle
        omega
      have hyr0 : y ^ r ≠ 0 := pow_ne_zero r hy0
      have hone : (1 : F) + y ^ r ≠ 0 :=
        gf24a9r_one_add_ne_zero_of_ord_pos a
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hpos)
      have hordw : w.ord (1 + y ^ r) = 0 :=
        gf24a9r_ord_one_add_of_ord_pos w hyr0
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hyw)
      have horda : a.ord (1 + y ^ r) = 0 :=
        gf24a9r_ord_one_add_of_ord_pos a hyr0
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hpos)
      refine ⟨z * (1 + y ^ r), mul_ne_zero hz0 hone, ?_, fun w' hw' => ?_⟩
      · rw [w.ord_mul hz0 hone, hordw]
        omega
      · rcases Finset.mem_insert.mp hw' with rfl | hw'S'
        · rw [w'.ord_mul hz0 hone, horda]
          omega
        · have hyneg : w'.ord (y ^ r) < 0 := by
            rw [gf24a9r_ord_pow]
            exact mul_neg_of_pos_of_neg (by omega) (hyS' w' hw'S')
          have hordw' : w'.ord (1 + y ^ r) = (r : ℤ) * w'.ord y := by
            rw [gf24a9r_ord_one_add_of_ord_neg w' hyr0 hyneg, gf24a9r_ord_pow]
          rw [w'.ord_mul hz0 hone, hordw']
          have h1 : w'.ord y ≤ -1 := by have := hyS' w' hw'S'; omega
          have h2 : (r : ℤ) * w'.ord y ≤ (r : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left h1 (by omega)
          have h3 := hrB w' hw'S'
          linarith

end Toolkit
section RowB

theorem gf24a9r_cotraceFiberLocalizedPolarApprox
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] :
    CotraceFiberLocalizedPolarApprox K F E := by
  intro _instE _instF ωE _hωE _hgen v w _hwfib n f hf
  classical
  set ωF := kaehlerPullback K F E ωE
  rcases eq_or_ne f 0 with rfl | hf0
  · refine ⟨0, ?_, fun w' _ _ => Submodule.zero_mem _⟩
    rw [sub_zero]
    exact Submodule.zero_mem _
  obtain ⟨u, hu0, huw, huS⟩ :=
    gf24a9r_exists_separator w ((v.fiber F).erase w) (Finset.notMem_erase w _)
  obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ (v.fiber F).erase w,
      -(w'.ord (f * w'.differentialCoeff ωF)) < (r : ℤ) := by
    refine ⟨((v.fiber F).erase w).sup
        (fun w' => (-(w'.ord (f * w'.differentialCoeff ωF))).toNat) + 1,
      Nat.le_add_left 1 _, fun w' hw' => ?_⟩
    have hle : (-(w'.ord (f * w'.differentialCoeff ωF))).toNat
        ≤ ((v.fiber F).erase w).sup
          (fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) :=
      Finset.le_sup (f := fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) hw'
    have h1 : -(w'.ord (f * w'.differentialCoeff ωF))
        ≤ ((-(w'.ord (f * w'.differentialCoeff ωF))).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((-(w'.ord (f * w'.differentialCoeff ωF))).toNat : ℤ)
        ≤ ((((v.fiber F).erase w).sup
          (fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) : ℕ) : ℤ) := by
      exact_mod_cast hle
    omega
  have hr1' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr1
  have hur0 : u ^ r ≠ 0 := pow_ne_zero r hu0
  have hone : (1 : F) + u ^ r ≠ 0 :=
    gf24a9r_one_add_ne_zero_of_ord_pos w
      (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) huw)
  have hinv0 : ((1 : F) + u ^ r)⁻¹ ≠ 0 := inv_ne_zero hone
  have hordw_one : w.ord (1 + u ^ r) = 0 :=
    gf24a9r_ord_one_add_of_ord_pos w hur0
      (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) huw)
  refine ⟨f * ((1 : F) + u ^ r)⁻¹, ?_, ?_⟩
  · have hdiff : f - f * ((1 : F) + u ^ r)⁻¹ = f * u ^ r * ((1 : F) + u ^ r)⁻¹ := by
      have hcancel := mul_inv_cancel₀ hone
      calc f - f * ((1 : F) + u ^ r)⁻¹
          = f * (((1 : F) + u ^ r) * ((1 : F) + u ^ r)⁻¹)
            - f * ((1 : F) + u ^ r)⁻¹ := by rw [hcancel, mul_one]
        _ = f * u ^ r * ((1 : F) + u ^ r)⁻¹ := by ring
    rw [hdiff]
    refine (w.mem_regularPoleSubmodule ωF n _).mpr ?_
    rcases eq_or_ne (w.differentialCoeff ωF) 0 with hdc | hdc
    · rw [hdc, mul_zero, mul_zero]
      exact zero_mem _
    · have hin : 0 ≤ w.ord (w.uniformizer ^ (n + 1) * (f * w.differentialCoeff ωF)) :=
        w.ord_nonneg_of_mem ((w.mem_regularPoleSubmodule ωF (n + 1) f).mp hf)
      rw [w.ord_mul (w.uniformizer_pow_ne_zero _) (mul_ne_zero hf0 hdc),
        w.ord_uniformizer_pow, w.ord_mul hf0 hdc] at hin
      have hX0 : f * u ^ r * ((1 : F) + u ^ r)⁻¹ ≠ 0 :=
        mul_ne_zero (mul_ne_zero hf0 hur0) hinv0
      refine w.mem_of_ord_nonneg
        (mul_ne_zero (w.uniformizer_pow_ne_zero n) (mul_ne_zero hX0 hdc)) ?_
      rw [w.ord_mul (w.uniformizer_pow_ne_zero n) (mul_ne_zero hX0 hdc),
        w.ord_uniformizer_pow, w.ord_mul hX0 hdc,
        w.ord_mul (mul_ne_zero hf0 hur0) hinv0, w.ord_mul hf0 hur0,
        w.ord_inv, hordw_one, gf24a9r_ord_pow]
      have hru : (1 : ℤ) ≤ (r : ℤ) * w.ord u := by
        have huw1 : (1 : ℤ) ≤ w.ord u := by omega
        nlinarith [hr1', huw1]
      push_cast at hin ⊢
      linarith
  · intro w' hw'fib hne
    have hw'S : w' ∈ (v.fiber F).erase w := Finset.mem_erase.mpr ⟨hne, hw'fib⟩
    have hu_neg : w'.ord u < 0 := huS w' hw'S
    refine (w'.mem_regularSubmodule ωF _).mpr ?_
    rcases eq_or_ne (w'.differentialCoeff ωF) 0 with hdc | hdc
    · rw [hdc, mul_zero]
      exact zero_mem _
    · have hre : f * ((1 : F) + u ^ r)⁻¹ * w'.differentialCoeff ωF
          = f * w'.differentialCoeff ωF * ((1 : F) + u ^ r)⁻¹ := by ring
      rw [hre]
      have hfdc : f * w'.differentialCoeff ωF ≠ 0 := mul_ne_zero hf0 hdc
      have hurneg : w'.ord (u ^ r) < 0 := by
        rw [gf24a9r_ord_pow]
        exact mul_neg_of_pos_of_neg (by omega) hu_neg
      have hordw' : w'.ord (1 + u ^ r) = (r : ℤ) * w'.ord u := by
        rw [gf24a9r_ord_one_add_of_ord_neg w' hur0 hurneg, gf24a9r_ord_pow]
      refine w'.mem_of_ord_nonneg (mul_ne_zero hfdc hinv0) ?_
      rw [w'.ord_mul hfdc hinv0, w'.ord_inv, hordw']
      have h1 : w'.ord u ≤ -1 := by omega
      have h2 : (r : ℤ) * w'.ord u ≤ (r : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left h1 (by omega)
      have h3 := hrB w' hw'S
      linarith

end RowB
end ModularCurve
end

noncomputable section

namespace AlgebraicCurve

section Additivity

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kaehlerResidueTermKFam_diagonal_add
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (v : Place K F) (g₁ g₂ : F) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F (g₁ + g₂)) v
      = kaehlerResidueTermKFam Rfam ω (diagonalHom K F g₁) v
        + kaehlerResidueTermKFam Rfam ω (diagonalHom K F g₂) v := by
  simp only [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  rw [add_mul, map_add, map_add]

theorem kaehlerResidueTermKFam_diagonal_zero
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (v : Place K F) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F (0 : F)) v = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply, zero_mul, _root_.map_zero, _root_.map_zero]

end Additivity
section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

theorem cotraceFiberIdentityK_zero
    [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    (ωE : Ω[E⁄K]) (v : Place K E) :
    ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F (0 : F)) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F (0 : F))) v := by
  rw [Finset.sum_eq_zero (fun w _ => kaehlerResidueTermKFam_diagonal_zero RfamF _ w),
    _root_.map_zero (Algebra.trace E F), kaehlerResidueTermKFam_diagonal_zero RfamE ωE v]

theorem cotraceFiberIdentityK_add
    [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (v : Place K E) {g p : F}
    (hg : ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F g) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F g)) v)
    (hp : ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F p) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v) :
    ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F (g + p)) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F (g + p))) v := by
  calc ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F (g + p)) w
      = ∑ w ∈ v.fiber F,
          (kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE) (diagonalHom K F g) w
            + kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
                (diagonalHom K F p) w) :=
        Finset.sum_congr rfl fun w _ =>
          kaehlerResidueTermKFam_diagonal_add RfamF (kaehlerPullback K F E ωE) w g p
    _ = (∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F g) w)
          + ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
              (diagonalHom K F p) w :=
        Finset.sum_add_distrib
    _ = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F g)) v
          + kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v := by
        rw [hg, hp]
    _ = kaehlerResidueTermKFam RfamE ωE
          (diagonalHom K E (Algebra.trace E F g + Algebra.trace E F p)) v :=
        (kaehlerResidueTermKFam_diagonal_add RfamE ωE v _ _).symm
    _ = kaehlerResidueTermKFam RfamE ωE
          (diagonalHom K E (Algebra.trace E F (g + p))) v := by
        rw [← map_add]

theorem cotraceFiberIdentityK_of_uniform_layer
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (hωE : ωE ≠ 0) (hgen : kaehlerPullback K F E ωE ≠ 0)
    (hA' : ∀ (v : Place K E) (p : F),
        (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
          p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
          p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F p) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v)
    (hB : CotraceFiberLocalizedPolarApprox K F E)
    (v : Place K E) :
    ∀ (N : ℕ) (f : F),
      (∀ w ∈ v.fiber F, f ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) N) →
      ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F f) w
        = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F f)) v := by
  intro N
  induction N with
  | zero =>
    intro f hf
    refine hA' v f ?_
    intro w₁ hw₁ w₂ hw₂ hp₁ hp₂
    exfalso
    have hreg := hf w₁ hw₁
    rw [Place.regularPoleSubmodule_zero] at hreg
    exact hp₁ hreg
  | succ N ih =>
    intro f hf
    classical
    choose! q hq1 hq2 using fun (w : Place K F) (hw : w ∈ v.fiber F) =>
      hB hωE hgen v w hw N f (hf w hw)
    have hrem : ∀ w₀ ∈ v.fiber F,
        f - ∑ w ∈ v.fiber F, q w
          ∈ w₀.regularPoleSubmodule (kaehlerPullback K F E ωE) N := by
      intro w₀ hw₀
      have hsplit : ∑ w ∈ v.fiber F, q w
          = q w₀ + ∑ w ∈ (v.fiber F).erase w₀, q w :=
        (Finset.add_sum_erase _ q hw₀).symm
      have heq : f - ∑ w ∈ v.fiber F, q w
          = (f - q w₀) - ∑ w ∈ (v.fiber F).erase w₀, q w := by
        rw [hsplit]; ring
      rw [heq]
      refine Submodule.sub_mem _ (hq1 w₀ hw₀) (Submodule.sum_mem _ ?_)
      intro w hw
      have hwfib : w ∈ v.fiber F := Finset.mem_of_mem_erase hw
      have hwne : w ≠ w₀ := Finset.ne_of_mem_erase hw
      have hq_reg : q w ∈ w₀.regularSubmodule (kaehlerPullback K F E ωE) :=
        hq2 w hwfib w₀ hw₀ (Ne.symm hwne)
      rw [← Place.regularPoleSubmodule_zero] at hq_reg
      exact w₀.regularPoleSubmodule_mono _ (Nat.zero_le N) hq_reg
    have hrem_ident := ih (f - ∑ w ∈ v.fiber F, q w) hrem
    have happrox_ident : ∀ w ∈ v.fiber F,
        ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F (q w)) w'
          = kaehlerResidueTermKFam RfamE ωE
              (diagonalHom K E (Algebra.trace E F (q w))) v := by
      intro w hw
      refine hA' v (q w) ?_
      intro w₁ hw₁ w₂ hw₂ hp₁ hp₂
      have h₁ : w₁ = w := by
        by_contra hne
        exact hp₁ (hq2 w hw w₁ hw₁ hne)
      have h₂ : w₂ = w := by
        by_contra hne
        exact hp₂ (hq2 w hw w₂ hw₂ hne)
      rw [h₁, h₂]
    have hsum_ident :
        ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F (∑ w ∈ v.fiber F, q w)) w'
          = kaehlerResidueTermKFam RfamE ωE
              (diagonalHom K E (Algebra.trace E F (∑ w ∈ v.fiber F, q w))) v :=
      Finset.sum_induction q
        (fun x => ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F x) w'
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F x)) v)
        (fun a b ha hb => cotraceFiberIdentityK_add RfamF RfamE v ha hb)
        (cotraceFiberIdentityK_zero RfamF RfamE ωE v)
        happrox_ident
    have hcombined := cotraceFiberIdentityK_add RfamF RfamE v hrem_ident hsum_ident
    rwa [sub_add_cancel] at hcombined

theorem fiberKaehlerCotraceResidueIdentityK_of_rowAK_rowB
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F E)
    (hB : CotraceFiberLocalizedPolarApprox K F E) :
    FiberKaehlerCotraceResidueIdentityK K F E := by
  intro instE instF RfamF ωE hωE hgen
  obtain ⟨RfamE, hA'⟩ := hA RfamF hωE hgen
  refine ⟨RfamE, fun v f => ?_⟩
  classical
  choose nfun hnfun using fun w : Place K F =>
    w.exists_mem_regularPoleSubmodule (kaehlerPullback K F E ωE) f
  refine cotraceFiberIdentityK_of_uniform_layer RfamF RfamE hωE hgen hA' hB v
    (∑ w ∈ v.fiber F, nfun w) f (fun w hw => ?_)
  exact w.regularPoleSubmodule_mono _
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw) (hnfun w)

end Engine
section RowBDischarged

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

theorem fiberKaehlerCotraceResidueIdentityK_of_rowAK
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F E) :
    FiberKaehlerCotraceResidueIdentityK K F E :=
  fiberKaehlerCotraceResidueIdentityK_of_rowAK_rowB hA
    (ModularCurve.gf24a9r_cotraceFiberLocalizedPolarApprox K F E)

end RowBDischarged
section CompositeRatFunc

variable {K F : Type*} [Field K] [IsAlgClosed K]
variable [Field F] [Algebra K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]

theorem residueTheoremK_of_rowAK_ratFunc_isAlgClosed
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F (RatFunc K)) :
    ResidueTheoremK K F := by
  classical
  exact
    residueTheoremK_of_cotraceResidueIdentityK_ratFunc_isAlgClosed hgen
      (fiberKaehlerCotraceResidueIdentityK_of_rowAK hA)

end CompositeRatFunc
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve

section DataKStarSeam

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTermKFam_dataKStar (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTermKFam (HasCanonicalLocalResidueKStar.dataKStar) ω α v
      = kaehlerResidueTerm ω α v := rfl

theorem kaehlerResidueTermKFam_eq_of_subsingleton
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K]) (α : Place K F → F)
    (v : Place K F) (hsub : Subsingleton v.CanonicalLocalResidueDataK) :
    kaehlerResidueTermKFam Rfam ω α v = kaehlerResidueTerm ω α v := by
  have hR : Rfam v = HasCanonicalLocalResidueKStar.dataKStar v := hsub.elim _ _
  rw [kaehlerResidueTermKFam_apply, hR]
  rfl

end DataKStarSeam
section AlgClosedSurj

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
private theorem surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue
    [IsAlgClosed K] (v : Place K F) [v.FiniteResidue] :
    Function.Surjective (algebraMap K v.ResidueField) := by
  have : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := v.ResidueField)).surjective

end Place
namespace Place
private theorem subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue
    [IsAlgClosed K] (v : Place K F) [v.FiniteResidue] :
    Subsingleton v.CanonicalLocalResidueDataK :=
  v.subsingleton_canonicalLocalResidueDataK_of_surj
    v.surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue

end Place
end AlgClosedSurj
section SubsingletonBridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

theorem cotraceResidueIdentityOnFiberLocalizedK_of_committed
    (hsubF : ∀ w : Place K F, Subsingleton w.CanonicalLocalResidueDataK)
    (h : CotraceResidueIdentityOnFiberLocalized K F E) :
    CotraceResidueIdentityOnFiberLocalizedK K F E := by
  intro _ _ RfamF ωE hωE hgen
  refine ⟨HasCanonicalLocalResidueKStar.dataKStar, fun v p hloc => ?_⟩
  calc ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F p) w
      = ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE)
          (diagonalHom K F p) w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        exact kaehlerResidueTermKFam_eq_of_subsingleton RfamF _ _ w (hsubF w)
    _ = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F p)) v :=
        h hωE hgen v p hloc
    _ = kaehlerResidueTermKFam (HasCanonicalLocalResidueKStar.dataKStar) ωE
          (diagonalHom K E (Algebra.trace E F p)) v :=
        (kaehlerResidueTermKFam_dataKStar ωE _ v).symm

end SubsingletonBridge
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve

section KaehlerPullbackSmul

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

theorem kw_mlc_hrtCharP7_kaehlerPullback_smul (g : E) (ωE : Ω[E⁄K]) :
    kaehlerPullback K F E (g • ωE) = (algebraMap E F g) • kaehlerPullback K F E ωE := by
  change (KaehlerDifferential.map K K E F) (g • ωE)
    = (algebraMap E F g) • (KaehlerDifferential.map K K E F) ωE
  rw [LinearMap.map_smul, algebra_compatible_smul F g]

end KaehlerPullbackSmul
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve

section FKCRIWire

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kw_mlc_hrtCharP9_cotraceResidueIdentityOnFiberLocalized_of_fkcri
    (h : FiberKaehlerCotraceResidueIdentity K F E) :
    CotraceResidueIdentityOnFiberLocalized K F E := by
  intro _ _ ωE hωE hgen v p _
  exact h hωE hgen v p

end FKCRIWire
section FKCRIProduction

variable {K F : Type*} [Field K] [IsAlgClosed K]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [∀ w : Place K F, w.FiniteResidue]

theorem residueTheoremK_of_fiberKaehlerCotraceResidueIdentity_ratFunc_isAlgClosed
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hFKCRI : FiberKaehlerCotraceResidueIdentity K F (RatFunc K)) :
    ResidueTheoremK K F := by
  classical
  exact
    residueTheoremK_of_rowAK_ratFunc_isAlgClosed hgen
      (cotraceResidueIdentityOnFiberLocalizedK_of_committed
        (fun w => w.subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue)
        (kw_mlc_hrtCharP9_cotraceResidueIdentityOnFiberLocalized_of_fkcri K F (RatFunc K)
          hFKCRI))

end FKCRIProduction
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

theorem kwHgfV352_localResidueCompletion_spec (v : Place K E) (xh : v.adicCompletion)
    {x : E} (hx : algebraMap E v.adicCompletion x - xh ∈ v.adicCompletionIntegers) :
    kwHgfV352LocalResidueCompletion v xh = v.localResidue x := by
  unfold kwHgfV352LocalResidueCompletion
  set x₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose
  have hx₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose_spec
  have heq : algebraMap E v.adicCompletion (x₀ - x)
      = (algebraMap E v.adicCompletion x₀ - xh) - (algebraMap E v.adicCompletion x - xh) := by
    rw [map_sub]; ring
  have hdiff : algebraMap E v.adicCompletion (x₀ - x) ∈ v.adicCompletionIntegers :=
    heq ▸ sub_mem hx₀ hx
  have hov : x₀ - x ∈ v.toValuationSubring :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mp hdiff
  have hzero : v.localResidue (x₀ - x) = 0 :=
    v.localResidue_eq_zero_of_ord_nonneg (Or.inr (v.ord_nonneg_of_mem hov))
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem kwHgfV352_localResidueCompletion_algebraMap (v : Place K E) (x : E) :
    kwHgfV352LocalResidueCompletion v (algebraMap E v.adicCompletion x)
      = v.localResidue x :=
  kwHgfV352_localResidueCompletion_spec v _
    (by rw [sub_self]; exact zero_mem _)

theorem kwHgfV352_localResidueCompletion_add (v : Place K E)
    (xh yh : v.adicCompletion) :
    kwHgfV352LocalResidueCompletion v (xh + yh)
      = kwHgfV352LocalResidueCompletion v xh
        + kwHgfV352LocalResidueCompletion v yh := by
  obtain ⟨x, hx⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh
  obtain ⟨y, hy⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v yh
  have heq : algebraMap E v.adicCompletion (x + y) - (xh + yh)
      = (algebraMap E v.adicCompletion x - xh) + (algebraMap E v.adicCompletion y - yh) := by
    rw [map_add]; ring
  rw [kwHgfV352_localResidueCompletion_spec v xh hx,
    kwHgfV352_localResidueCompletion_spec v yh hy,
    kwHgfV352_localResidueCompletion_spec v (xh + yh) (x := x + y)
      (heq ▸ add_mem hx hy),
    map_add]

theorem kwHgfV352_localResidueCompletion_sum (v : Place K E) {ι : Type*}
    (s : Finset ι) (f : ι → v.adicCompletion) :
    kwHgfV352LocalResidueCompletion v (∑ i ∈ s, f i)
      = ∑ i ∈ s, kwHgfV352LocalResidueCompletion v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (0 : v.adicCompletion) = algebraMap E v.adicCompletion 0 from (_root_.map_zero _).symm,
      kwHgfV352_localResidueCompletion_algebraMap, _root_.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, kwHgfV352_localResidueCompletion_add, ih,
      Finset.sum_insert ha]

end LocalResidueCompletion
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve

section ChainRule

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Nontrivial Ω[F⁄K]]

theorem Place.differentialCoeff_kaehlerPullback
    (v : Place K E) [v.DCoordGenerates] (w : Place K F) [w.DCoordGenerates]
    (ωE : Ω[E⁄K]) :
    w.differentialCoeff (kaehlerPullback K F E ωE)
      = algebraMap E F (v.differentialCoeff ωE)
        * w.differentialCoeff (kaehlerPullback K F E v.dCoord) := by
  conv_lhs => rw [← v.differentialCoeff_smul_dCoord ωE,
    kw_mlc_hrtCharP7_kaehlerPullback_smul, w.differentialCoeff_smul]

end ChainRule
end AlgebraicCurve
end

noncomputable section

namespace AlgebraicCurve

section OmegaShift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K F]
variable [Nontrivial Ω[F⁄K]]

theorem kaehlerResidueTerm_kaehlerPullback_diagonal_eq_dCoord_shift
    (v : Place K E) [v.DCoordGenerates]
    (w : Place K F) [w.DCoordGenerates] (ωE : Ω[E⁄K]) (g : F) :
    kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F g) w
      = kaehlerResidueTerm (kaehlerPullback K F E v.dCoord)
          (diagonalHom K F (g * algebraMap E F (v.differentialCoeff ωE))) w := by
  unfold kaehlerResidueTerm
  congr 2
  change g * w.differentialCoeff (kaehlerPullback K F E ωE)
    = g * algebraMap E F (v.differentialCoeff ωE)
        * w.differentialCoeff (kaehlerPullback K F E v.dCoord)
  rw [Place.differentialCoeff_kaehlerPullback v w ωE, mul_assoc]

end OmegaShift
end AlgebraicCurve
end

noncomputable section

namespace ModularCurve

section CompletionTraceAtLinear

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K F]

omit [HasPrincipalDivisors K F] in
theorem kwF4R1V391a_completionTraceF'_mul_algebraMap (w : Place K F) (g : F) (c : E) :
    kwFfgcCompletionTraceF' E w (g * algebraMap E F c)
      = kwFfgcCompletionTraceF' E w g
          * algebraMap E (w.restrict E).adicCompletion c := by
  rw [kw_ffgc_completionTraceF'_apply, kw_ffgc_completionTraceF'_apply, map_mul,
    kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w c,
    mul_comm (algebraMap F w.adicCompletion g) _, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem kwF4R1V391a_completionTraceAt_mul_algebraMap
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F) (c : E) :
    kwHgfV352CompletionTraceAt v w hw (g * algebraMap E F c)
      = kwHgfV352CompletionTraceAt v w hw g * algebraMap E v.adicCompletion c := by
  have hv : w.restrict E = v := Place.mem_fiber.mp hw
  subst hv
  change (Place.mem_fiber.mp hw ▸ kwFfgcCompletionTraceF' E w (g * algebraMap E F c))
    = (Place.mem_fiber.mp hw ▸ kwFfgcCompletionTraceF' E w g)
        * algebraMap E (w.restrict E).adicCompletion c
  rw [kwF4R1V391a_completionTraceF'_mul_algebraMap w g c]

end CompletionTraceAtLinear

end ModularCurve

end

section

namespace FLT
namespace Gapsw7X3xCrossPlaceTraceDecomposition

open scoped NumberField TensorProduct

theorem gapsw7_x3x_trace_pi (R : Type*) [CommRing R] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)]
    (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  have _em := Classical.em
  classical
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (S i)) R (S i) :=
    fun i => Module.Free.chooseBasis R (S i)
  have key : Algebra.leftMulMatrix (Pi.basis b) x
      = Matrix.blockDiagonal' (fun i => Algebra.leftMulMatrix (b i) (x i)) := by
    refine Matrix.ext fun ji ji' => ?_
    obtain ⟨i, j⟩ := ji
    obtain ⟨i', j'⟩ := ji'
    rcases eq_or_ne i i' with rfl | hne
    · rw [Matrix.blockDiagonal'_apply_eq, Algebra.leftMulMatrix_eq_repr_mul,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i (b i j')) i = x i * b i j' := by
        simp
      rw [hx]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i' (b i' j')) i = 0 := by
        simp [Pi.single_eq_of_ne hne]
      rw [hx]
      simp
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), key,
    Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ =>
    (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

theorem gapsw7_x3x_trace_baseChange (R A B : Type*) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Free R B]
    [Module.Finite R B] (b : B) :
    Algebra.trace A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b)
      = algebraMap R A (Algebra.trace R B b) := by
  have _em := Classical.em
  have h := LinearMap.trace_baseChange (Algebra.lmul R B b) A
  rw [Algebra.baseChange_lmul] at h
  exact h

theorem gapsw7_x3x_trace_decomposition_of_prod_iso (R A B : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    [∀ i, Module.Free A (S i)] [∀ i, Module.Finite A (S i)]
    (e : (A ⊗[R] B) ≃ₐ[A] ∀ i, S i) (b : B) :
    algebraMap R A (Algebra.trace R B b)
      = ∑ i, Algebra.trace A (S i) (e ((1 : A) ⊗ₜ[R] b) i) := by
  have _em := Classical.em
  rw [← gapsw7_x3x_trace_baseChange R A B b,
    ← Algebra.trace_eq_of_algEquiv e ((1 : A) ⊗ₜ[R] b),
    gapsw7_x3x_trace_pi A S]

end Gapsw7X3xCrossPlaceTraceDecomposition
end FLT
end

noncomputable section

namespace ModularCurve
namespace KwF4R1V384a

section FiberAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

scoped instance kwF4R1V384a_instAlgebraFiberCompletion (v : Place K E) (w' : v.fiber F) :
    Algebra v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kwFfgcAlgebraAdicCompletionComap E w'

scoped instance kwF4R1V384a_instIsScalarTowerFiberCompletion (v : Place K E) (w' : v.fiber F) :
    IsScalarTower E v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  refine IsScalarTower.of_algebraMap_eq fun e => ?_
  rw [show algebraMap E w'.adicCompletion e = algebraMap F w'.adicCompletion (algebraMap E F e)
    from IsScalarTower.algebraMap_apply E F w'.adicCompletion e]
  exact kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w' e

scoped instance kwF4R1V384a_instFiniteDimensionalFiberCompletion [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) :
    FiniteDimensional v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kw_ffgc_finiteDimensional_adicCompletion E w'

end FiberAlgebra
section SemilocalDiag

variable {K : Type*} (F : Type*) [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

def kwF4R1V384a_semilocalComponent (v : Place K E) (w' : v.fiber F) :
    v.adicCompletion ⊗[E] F →ₐ[v.adicCompletion] w'.1.adicCompletion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.adicCompletion w'.1.adicCompletion)
    (IsScalarTower.toAlgHom E F w'.1.adicCompletion) (fun _ _ => mul_comm _ _)

omit [HasPrincipalDivisors K E] in
@[scoped simp]
theorem kwF4R1V384a_semilocalComponent_tmul (v : Place K E) (w' : v.fiber F)
    (c : v.adicCompletion) (g : F) :
    kwF4R1V384a_semilocalComponent F v w' (c ⊗ₜ[E] g)
      = algebraMap v.adicCompletion w'.1.adicCompletion c
          * algebraMap F w'.1.adicCompletion g := by
  rfl

def kwF4R1V384a_semilocalDiag (v : Place K E) :
    v.adicCompletion ⊗[E] F →ₐ[v.adicCompletion]
      ((w' : v.fiber F) → w'.1.adicCompletion) :=
  AlgHom.pi (kwF4R1V384a_semilocalComponent F v)

variable {F}

omit [HasPrincipalDivisors K E] in
@[scoped simp]
theorem kwF4R1V384a_semilocalDiag_apply (v : Place K E) (x : v.adicCompletion ⊗[E] F)
    (w' : v.fiber F) :
    kwF4R1V384a_semilocalDiag F v x w' = kwF4R1V384a_semilocalComponent F v w' x := rfl

omit [HasPrincipalDivisors K E] in
theorem kwF4R1V384a_semilocalDiag_one_tmul (v : Place K E) (g : F) (w' : v.fiber F) :
    kwF4R1V384a_semilocalDiag F v ((1 : v.adicCompletion) ⊗ₜ[E] g) w'
      = algebraMap F w'.1.adicCompletion g := by
  rw [kwF4R1V384a_semilocalDiag_apply, kwF4R1V384a_semilocalComponent_tmul,
    map_one, one_mul]

end SemilocalDiag
section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

def KwF4R1V384aCompletionSemilocalBij : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E),
    Function.Bijective (kwF4R1V384a_semilocalDiag (K := K) (E := E) F v)

end Mint
section PerComponentSurjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K F]
variable [FiniteDimensional E F]

omit [HasPrincipalDivisors K F] [FiniteDimensional E F] in
theorem kwF4R1V384a_completionLinearCombination_surjective
    (w' : Place K F) {ι : Type*} [Fintype ι] (b : Module.Basis ι E F) :
    Function.Surjective (kwFfgcCompletionLinearCombination E w' b) := by
  let := kwFfgcRankOneAdicCompletion (K := K) (w'.restrict E)
  let : NontriviallyNormedField (w'.restrict E).adicCompletion :=
    Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion
      (WithZero (Multiplicative ℤ))
  rw [← Set.range_eq_univ, ← LinearMap.coe_range,
    ← (LinearMap.range (kwFfgcCompletionLinearCombination E w' b))
        |>.closed_of_finiteDimensional.closure_eq]
  exact (kw_ffgc_denseRange_completionLinearCombination E w' b).closure_range

theorem kwF4R1V384a_semilocalComponent_surjective (v : Place K E) (w' : v.fiber F) :
    Function.Surjective (kwF4R1V384a_semilocalComponent F v w') := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  intro y
  let b := Module.finBasis E F
  obtain ⟨c, hc⟩ := kwF4R1V384a_completionLinearCombination_surjective w' b y
  refine ⟨∑ i, c i ⊗ₜ[E] b i, ?_⟩
  rw [map_sum, ← hc]
  unfold kwFfgcCompletionLinearCombination
  rw [Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kwF4R1V384a_semilocalComponent_tmul, Algebra.smul_def]

end PerComponentSurjective
section SpecificMints

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

def KwF4R1V384aDistinctKernels : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' w'' : v.fiber F), w' ≠ w'' →
    RingHom.ker (kwF4R1V384a_semilocalComponent (K := K) (E := E) F v w').toRingHom
      ≠ RingHom.ker (kwF4R1V384a_semilocalComponent (K := K) (E := E) F v w'').toRingHom

def KwF4R1V384aFinrankCompletionEF : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F),
    (Module.finrank v.adicCompletion w'.1.adicCompletion : ℤ)
      = (w'.1.ramificationIndex E : ℤ) * (w'.1.inertiaDeg E : ℤ)

end SpecificMints
section BijEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

scoped instance kwF4R1V384a_ker_semilocalComponent_isMaximal
    [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) :
    (RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (kwF4R1V384a_semilocalComponent F v w').toRingHom
    (kwF4R1V384a_semilocalComponent_surjective v w')

theorem kwF4R1V384a_semilocalDiag_surjective_of_distinctKernels
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (hdist : KwF4R1V384aDistinctKernels K F E) (v : Place K E) :
    Function.Surjective (kwF4R1V384a_semilocalDiag F v) := by
  classical
  intro y
  let m : v.fiber F → Ideal (v.adicCompletion ⊗[E] F) :=
    fun w' => RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom
  have : ∀ w', (m w').IsMaximal :=
    kwF4R1V384a_ker_semilocalComponent_isMaximal v
  have hcop : Pairwise (Function.onFun IsCoprime m) := fun i j hij =>
    Ideal.isCoprime_of_isMaximal (I := m i) (J := m j) (hdist v i j hij)
  choose xw hxw using fun w' => kwF4R1V384a_semilocalComponent_surjective v w' (y w')
  obtain ⟨xbar, hxbar⟩ :=
    Ideal.quotientInfToPiQuotient_surj hcop (fun w' => Ideal.Quotient.mk (m w') (xw w'))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, funext fun w' => ?_⟩
  change kwF4R1V384a_semilocalComponent F v w' x = y w'
  have hcomp : Ideal.Quotient.mk (m w') x = Ideal.Quotient.mk (m w') (xw w') := by
    have := congrFun hxbar w'
    rwa [Ideal.quotientInfToPiQuotient_mk' m x w'] at this
  have hmod : x - xw w' ∈ m w' := Ideal.Quotient.eq.mp hcomp
  have hzero : kwF4R1V384a_semilocalComponent F v w' (x - xw w') = 0 := hmod
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, hxw w']

scoped instance kwF4R1V384a_instModuleFiberCompletion
    [HasPrincipalDivisors K F]
    (v : Place K E) (w' : v.fiber F) :
    Module v.adicCompletion w'.1.adicCompletion :=
  Algebra.toModule

theorem kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF
    [Algebra.IsSeparable E F]
    (hdist : KwF4R1V384aDistinctKernels K F E)
    (hef : KwF4R1V384aFinrankCompletionEF K F E) :
    KwF4R1V384aCompletionSemilocalBij K F E := by
  intro _ _ _ v
  have hsurj := kwF4R1V384a_semilocalDiag_surjective_of_distinctKernels hdist v
  refine ⟨?_, hsurj⟩
  let srPi : Semiring ((w' : v.fiber F) → w'.1.adicCompletion) := inferInstance
  let algPi : Algebra v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) :=
    inferInstance
  let modPi : Module v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) :=
    @Algebra.toModule _ _ _ srPi algPi
  have hdimcod : Module.finrank v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion)
      = Module.finrank E F := by
    have hpi : (Module.finrank v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) : ℕ)
        = ∑ w' : v.fiber F, Module.finrank v.adicCompletion w'.1.adicCompletion := by
      convert Module.finrank_pi_fintype v.adicCompletion using 2 <;>
        exact fun i => inferInstance
    rw [hpi]
    have hsum := Place.sum_ramificationIndex_mul_inertiaDeg (K := K) (F := E) (F' := F) v
    rw [← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    calc ∑ w' : v.fiber F,
          ((Module.finrank v.adicCompletion w'.1.adicCompletion : ℤ))
        = ∑ w' : v.fiber F,
            ((w'.1.ramificationIndex E : ℤ) * (w'.1.inertiaDeg E : ℤ)) :=
          Finset.sum_congr rfl fun w' _ => hef v w'
      _ = ∑ w' ∈ v.fiber F,
            ((w'.ramificationIndex E : ℤ) * (w'.inertiaDeg E : ℤ)) :=
          Finset.sum_attach (v.fiber F)
            (fun w => (w.ramificationIndex E : ℤ) * (w.inertiaDeg E : ℤ))
      _ = (Module.finrank E F : ℤ) := hsum
  have hdimdom : Module.finrank v.adicCompletion (v.adicCompletion ⊗[E] F)
      = Module.finrank E F := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  have hsurj' : Function.Surjective
      (kwF4R1V384a_semilocalDiag F v).toLinearMap := hsurj
  have fdPi : FiniteDimensional v.adicCompletion
      ((w' : v.fiber F) → w'.1.adicCompletion) := inferInstance
  exact (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    v.adicCompletion (v.adicCompletion ⊗[E] F) _ _ _
    ((w' : v.fiber F) → w'.1.adicCompletion) _ modPi _ fdPi
    (hdimdom.trans hdimcod.symm)
    (kwF4R1V384a_semilocalDiag F v).toLinearMap).mpr hsurj'

end BijEngine
section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

open FLT.Gapsw7X3xCrossPlaceTraceDecomposition

theorem kwF4R1V384a_trace_algebraMap_eq_completionTraceAt
    [HasPrincipalDivisors K F]
    (v : Place K E) (w' : v.fiber F) (g : F) :
    Algebra.trace v.adicCompletion w'.1.adicCompletion (algebraMap F w'.1.adicCompletion g)
      = AlgebraicCurve.kwHgfV352CompletionTraceAt v w'.1 w'.2 g := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  rfl

theorem kwF4R1V384a_completionTraceSum_of_semilocalBij
    (hbij : KwF4R1V384aCompletionSemilocalBij K F E) :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E := by
  classical
  intro _ _ _ v g
  let e : v.adicCompletion ⊗[E] F ≃ₐ[v.adicCompletion]
      ((w' : v.fiber F) → w'.1.adicCompletion) :=
    AlgEquiv.ofBijective (kwF4R1V384a_semilocalDiag F v) (hbij v)
  have : ∀ w' : v.fiber F, Module.Free v.adicCompletion w'.1.adicCompletion :=
    fun _ => Module.Free.of_divisionRing _ _
  rw [gapsw7_x3x_trace_decomposition_of_prod_iso E v.adicCompletion F
        (fun w' : v.fiber F => w'.1.adicCompletion) e g]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [show e ((1 : v.adicCompletion) ⊗ₜ[E] g) w'
      = kwF4R1V384a_semilocalDiag F v ((1 : v.adicCompletion) ⊗ₜ[E] g) w' from rfl,
    kwF4R1V384a_semilocalDiag_one_tmul,
    kwF4R1V384a_trace_algebraMap_eq_completionTraceAt]

theorem kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF
    [Algebra.IsSeparable E F]
    (hdist : KwF4R1V384aDistinctKernels K F E)
    (hef : KwF4R1V384aFinrankCompletionEF K F E) :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V384a_completionTraceSum_of_semilocalBij
    (kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF hdist hef)

end Headline
end KwF4R1V384a
end ModularCurve
end

noncomputable section

namespace ModularCurve
namespace KwF4R1V386a

open ModularCurve.KwF4R1V384a

section IsSeparableLift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_isSeparable_algebraMap_fiberCompletion
    [HasPrincipalDivisors K F]
    [Algebra.IsSeparable E F]
    (v : Place K E) (w' : v.fiber F) (g : F) :
    IsSeparable v.adicCompletion (algebraMap F w'.1.adicCompletion g) := by
  have hroot : Polynomial.aeval (R := v.adicCompletion)
      (algebraMap F w'.1.adicCompletion g)
      ((minpoly E g).map (algebraMap E v.adicCompletion)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap,
      show algebraMap F w'.1.adicCompletion g
          = IsScalarTower.toAlgHom E F w'.1.adicCompletion g from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, _root_.map_zero]
  have hmapsep : ((minpoly E g).map (algebraMap E v.adicCompletion)).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable E g)
  exact hmapsep.of_dvd (minpoly.dvd v.adicCompletion _ hroot)

theorem kwF4R1V386a_isSeparable_fiberCompletion
    [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (v : Place K E) (w' : v.fiber F) :
    Algebra.IsSeparable v.adicCompletion w'.1.adicCompletion := by
  have hgen : Algebra.adjoin v.adicCompletion
      (Set.range (algebraMap F w'.1.adicCompletion)) = ⊤ := by
    rw [Algebra.eq_top_iff]
    intro y
    obtain ⟨x, rfl⟩ := kwF4R1V384a_semilocalComponent_surjective v w' y
    induction x using TensorProduct.inductionOn with
    | tmul c g =>
      rw [kwF4R1V384a_semilocalComponent_tmul, ← Algebra.smul_def]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self g)) c
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  have hsep : ∀ x ∈ Set.range (algebraMap F w'.1.adicCompletion),
      IsSeparable v.adicCompletion x := by
    rintro _ ⟨g, rfl⟩
    exact kwF4R1V386a_isSeparable_algebraMap_fiberCompletion v w' g
  have hgenI : IntermediateField.adjoin v.adicCompletion
      (Set.range (algebraMap F w'.1.adicCompletion)) = ⊤ := by
    rw [eq_top_iff]; intro x _
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (hgen ▸ Algebra.mem_top)
  have hsepAdj : Algebra.IsSeparable v.adicCompletion
      (IntermediateField.adjoin v.adicCompletion
        (Set.range (algebraMap F w'.1.adicCompletion))) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable v.adicCompletion
      w'.1.adicCompletion).mpr hsep
  rw [hgenI] at hsepAdj
  exact Algebra.IsSeparable.of_algHom v.adicCompletion
    (⊤ : IntermediateField v.adicCompletion w'.1.adicCompletion)
    (IntermediateField.topEquiv (F := v.adicCompletion)
      (E := w'.1.adicCompletion)).symm.toAlgHom

end IsSeparableLift
section DistinctKernels

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_spectralNorm_eq_absoluteValue [FiniteDimensional E F]
    (w' : Place K F) (y : w'.adicCompletion) :
    letI := kwFfgcRankOneAdicCompletion (w'.restrict E)
    letI : NontriviallyNormedField (w'.restrict E).adicCompletion :=
      Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion ℤᵐ⁰
    spectralNorm (w'.restrict E).adicCompletion w'.adicCompletion y
      = kwFfgcAbsoluteValue E w' y := by
  let := kwFfgcRankOneAdicCompletion (w'.restrict E)
  let : NontriviallyNormedField (w'.restrict E).adicCompletion :=
    Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion ℤᵐ⁰
  have : IsUltrametricDist (w'.restrict E).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  have : Algebra.IsAlgebraic (w'.restrict E).adicCompletion w'.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  exact (spectralNorm_unique_field_norm_ext (f := kwFfgcAbsoluteValue E w')
    (kw_ffgc_absoluteValue_extends E w') y).symm

theorem kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber
    [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) (y : w'.1.adicCompletion) :
    letI := kwFfgcRankOneAdicCompletion v
    letI : NontriviallyNormedField v.adicCompletion :=
      Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
    spectralNorm v.adicCompletion w'.1.adicCompletion y
      = kwFfgcAbsoluteValue E w'.1 y := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kwF4R1V386a_spectralNorm_eq_absoluteValue (K := K) (E := E) w' y

theorem kwF4R1V386a_valuedAlgebraMap_le_one_iff (w' : Place K F) (g : F) :
    Valued.v (algebraMap F w'.adicCompletion g) ≤ 1 ↔ g ∈ w'.toValuationSubring := by
  have hval : Valued.v (algebraMap F w'.adicCompletion g) = w'.adicValuation g :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (v := w'.heightOneSpectrum) (K := F) g
  rw [hval]
  rcases eq_or_ne g 0 with rfl | hg
  · simp only [_root_.map_zero, zero_le_one, w'.toValuationSubring.zero_mem]
  · rw [w'.mem_iff_ord_nonneg hg, Place.ord, neg_nonneg]
    have hvne : w'.adicValuation g ≠ 0 := w'.adicValuation_ne_zero hg
    rw [show (0 : ℤ) = WithZero.log (1 : ℤᵐ⁰) from WithZero.log_one.symm]
    exact ⟨fun hle => WithZero.log_le_log hvne one_ne_zero |>.mpr hle,
      fun hlog => (WithZero.log_le_log hvne one_ne_zero).mp hlog⟩

omit [Algebra K E] [IsScalarTower K E F] in
theorem kwF4R1V386a_absoluteValue_algebraMap_le_one_iff
    (w' : Place K F) (g : F) :
    kwFfgcAbsoluteValue E w' (algebraMap F w'.adicCompletion g) ≤ 1
      ↔ g ∈ w'.toValuationSubring := by
  let := kwFfgcRankOneAdicCompletion w'
  have hr : (0 : ℝ) < ((w'.ramificationIndex E : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (w'.ramificationIndex_pos (F := E)))
  change ‖algebraMap F w'.adicCompletion g‖ ^ ((w'.ramificationIndex E : ℝ))⁻¹ ≤ 1
    ↔ g ∈ w'.toValuationSubring
  constructor
  · intro hle
    have hn : ‖algebraMap F w'.adicCompletion g‖ ≤ 1 := by
      by_contra hgt
      have hgt' : 1 < ‖algebraMap F w'.adicCompletion g‖ := not_le.mp hgt
      exact absurd ((Real.one_lt_rpow_iff_of_pos (lt_trans one_pos hgt')).mpr
        (Or.inl ⟨hgt', hr⟩)) (not_lt.mpr hle)
    rw [Valued.toNormedField.norm_le_one_iff] at hn
    exact (kwF4R1V386a_valuedAlgebraMap_le_one_iff w' g).mp hn
  · intro hmem
    have hn : ‖algebraMap F w'.adicCompletion g‖ ≤ 1 := by
      rw [Valued.toNormedField.norm_le_one_iff]
      exact (kwF4R1V386a_valuedAlgebraMap_le_one_iff w' g).mpr hmem
    calc ‖algebraMap F w'.adicCompletion g‖ ^ ((w'.ramificationIndex E : ℝ))⁻¹
        ≤ 1 ^ ((w'.ramificationIndex E : ℝ))⁻¹ :=
          Real.rpow_le_rpow (norm_nonneg _) hn hr.le
      _ = 1 := Real.one_rpow _

theorem kwF4R1V386a_distinctKernels :
    KwF4R1V384aDistinctKernels K F E := by
  intro _ _ _ v w' w'' hne hker
  apply hne
  have hsurj' := kwF4R1V384a_semilocalComponent_surjective v w'
  have hann : ∀ a ∈ RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom,
      kwF4R1V384a_semilocalComponent F v w'' a = 0 := fun a ha => by
    have : a ∈ RingHom.ker (kwF4R1V384a_semilocalComponent F v w'').toRingHom :=
      hker ▸ ha
    exact this
  let σ : w'.1.adicCompletion →ₐ[v.adicCompletion] w''.1.adicCompletion :=
    (Ideal.Quotient.liftₐ _ (kwF4R1V384a_semilocalComponent F v w'') hann).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj').symm.toAlgHom
  have hσcomp : ∀ x, σ (kwF4R1V384a_semilocalComponent F v w' x)
      = kwF4R1V384a_semilocalComponent F v w'' x := by
    intro x
    have hstep1 : (Ideal.quotientKerAlgEquivOfSurjective hsurj').symm
        (kwF4R1V384a_semilocalComponent F v w' x) = Ideal.Quotient.mk _ x := by
      rw [show kwF4R1V384a_semilocalComponent F v w' x
          = Ideal.quotientKerAlgEquivOfSurjective hsurj' (Ideal.Quotient.mk _ x) from rfl,
        AlgEquiv.symm_apply_apply]
    exact congrArg (Ideal.Quotient.liftₐ _ (kwF4R1V384a_semilocalComponent F v w'') hann) hstep1
  have hσF : ∀ g : F, σ (algebraMap F w'.1.adicCompletion g)
      = algebraMap F w''.1.adicCompletion g := by
    intro g
    have h' := hσcomp ((1 : v.adicCompletion) ⊗ₜ[E] g)
    rwa [kwF4R1V384a_semilocalComponent_tmul, map_one, one_mul,
      kwF4R1V384a_semilocalComponent_tmul, map_one, one_mul] at h'
  let := kwFfgcRankOneAdicCompletion v
  let : NontriviallyNormedField v.adicCompletion :=
    Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hσspec : ∀ y, spectralNorm v.adicCompletion w''.1.adicCompletion (σ y)
      = spectralNorm v.adicCompletion w'.1.adicCompletion y := by
    intro y
    unfold spectralNorm
    congr 1
    exact minpoly.algHom_eq σ hσinj y
  refine Subtype.ext ?_
  refine AlgebraicCurve.Place.ext (K := K) (F := F) (SetLike.ext fun g => ?_)
  rw [← kwF4R1V386a_absoluteValue_algebraMap_le_one_iff (K := K) (E := E) w'.1 g,
    ← kwF4R1V386a_absoluteValue_algebraMap_le_one_iff (K := K) (E := E) w''.1 g,
    ← kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber (K := K) (E := E) v w'
      (algebraMap F w'.1.adicCompletion g),
    ← kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber (K := K) (E := E) v w''
      (algebraMap F w''.1.adicCompletion g),
    ← hσF g, hσspec]

end DistinctKernels
section FinrankCompletionEF

open Valuation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_ramificationIdx_completion_eq
    (w' : Place K F) :
    (maximalIdeal (w'.restrict E).adicCompletionIntegers).ramificationIdx'
      (maximalIdeal w'.adicCompletionIntegers) = w'.ramificationIndex E := by
  set e := w'.ramificationIndex E with he
  have hepos : 0 < e := w'.ramificationIndex_pos (F := E)
  obtain ⟨π, hπval⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer E
    (w'.restrict E).heightOneSpectrum
  have hmap : (maximalIdeal (w'.restrict E).adicCompletionIntegers).map
      (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers)
        = Ideal.span {algebraMap _ w'.adicCompletionIntegers π} := by
    rw [show maximalIdeal ((w'.restrict E).adicCompletionIntegers : Type _)
        = (w'.restrict E).heightOneSpectrum.completionIdeal E from rfl,
      IsDedekindDomain.HeightOneSpectrum.completionIdeal,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer E
        _ hπval,
      Ideal.map_span, Set.image_singleton]
  have hπval' : Valued.v (π : (w'.restrict E).adicCompletion)
      = (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤᵐ⁰) := hπval
  have hval : Valued.v ((algebraMap (w'.restrict E).adicCompletionIntegers
        w'.adicCompletionIntegers π : w'.adicCompletionIntegers) : w'.adicCompletion)
      = (↑(Multiplicative.ofAdd (-(e : ℤ))) : ℤᵐ⁰) := by
    rw [show ((algebraMap _ w'.adicCompletionIntegers π
          : w'.adicCompletionIntegers) : w'.adicCompletion)
        = kwFfgcAdicCompletionComap E w' (π : (w'.restrict E).adicCompletion) from
      (kw_ffgc_adicCompletionComapIntegers_coe E w' π).symm,
      kw_ffgc_valued_adicCompletionComap, hπval', ← WithZero.coe_pow, WithZero.coe_inj,
      ← ofAdd_nsmul, nsmul_eq_mul, mul_neg_one, he]
  refine Ideal.ramificationIdx'_spec ?_ ?_
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      show maximalIdeal (w'.adicCompletionIntegers : Type _)
        = w'.heightOneSpectrum.completionIdeal F from rfl,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow, hval]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      show maximalIdeal (w'.adicCompletionIntegers : Type _)
        = w'.heightOneSpectrum.completionIdeal F from rfl,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow, hval]
    simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le, not_le]
    omega

theorem kwF4R1V386a_integersToCompletion_commute
    (w' : Place K F) (a : (w'.restrict E).toValuationSubring) :
    algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers
        (algebraMap (w'.restrict E).toValuationSubring
          (w'.restrict E).adicCompletionIntegers a)
      = algebraMap w'.toValuationSubring w'.adicCompletionIntegers
          (restrictInclusion E w' a) := by
  apply Subtype.ext
  exact (kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w' (a : E)).symm

theorem kwF4R1V386a_inertiaDeg_completion_eq
    (w' : Place K F) :
    (maximalIdeal w'.adicCompletionIntegers).inertiaDeg
      (w'.restrict E).adicCompletionIntegers = w'.inertiaDeg E := by
  have : IsLocalHom (algebraMap (w'.restrict E).adicCompletionIntegers
      w'.adicCompletionIntegers) :=
    kw_ffgc_isLocalHom_adicCompletionComapIntegers E w'
  have : (maximalIdeal w'.adicCompletionIntegers).LiesOver
      (maximalIdeal (w'.restrict E).adicCompletionIntegers) := by
    have hcomap : (maximalIdeal w'.adicCompletionIntegers).comap
        (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers)
        = maximalIdeal (w'.restrict E).adicCompletionIntegers :=
      ((IsLocalRing.local_hom_TFAE (algebraMap (w'.restrict E).adicCompletionIntegers
        w'.adicCompletionIntegers)).out 1 5).mp ‹IsLocalHom _›
    exact ⟨hcomap.symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal
    (maximalIdeal (w'.restrict E).adicCompletionIntegers)
    (maximalIdeal w'.adicCompletionIntegers)]
  symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (kw_ffgc_residueFieldEquivCompletionResidueField (w'.restrict E))
    (kw_ffgc_residueFieldEquivCompletionResidueField w') ?_
  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact congrArg (IsLocalRing.residue w'.adicCompletionIntegers)
    (kwF4R1V386a_integersToCompletion_commute (K := K) (E := E) w' a)

theorem kwF4R1V386a_finrankCompletionEF [Algebra.IsSeparable E F] :
    KwF4R1V384aFinrankCompletionEF K F E := by
  intro _ _ _ v wfib
  have hv : wfib.1.restrict E = v := Place.mem_fiber.mp wfib.2
  have hsep : Algebra.IsSeparable v.adicCompletion wfib.1.adicCompletion :=
    kwF4R1V386a_isSeparable_fiberCompletion v wfib
  rcases wfib with ⟨w', hw'⟩
  dsimp only at hv hsep ⊢
  subst hv
  have : Algebra.IsSeparable (w'.restrict E).adicCompletion w'.adicCompletion := hsep
  have : Algebra.IsAlgebraic (w'.restrict E).adicCompletion w'.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  have : IsIntegralClosure w'.adicCompletionIntegers
      (w'.restrict E).adicCompletionIntegers w'.adicCompletion :=
    kw_ffgc_isIntegralClosure_adicCompletionIntegers E w'
  have : IsNoetherian (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    IsIntegralClosure.isNoetherian (w'.restrict E).adicCompletionIntegers
      (w'.restrict E).adicCompletion w'.adicCompletion w'.adicCompletionIntegers
  have : Module.Finite (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    Module.IsNoetherian.finite _ _
  have hinj : Function.Injective
      (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletion) := by
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap (w'.restrict E).adicCompletion w'.adicCompletion).injective
    simpa [IsScalarTower.algebraMap_apply
      (w'.restrict E).adicCompletionIntegers
      (w'.restrict E).adicCompletion w'.adicCompletion] using hxy
  let : Module.IsTorsionFree
      (w'.restrict E).adicCompletionIntegers w'.adicCompletion :=
    Module.IsTorsionFree.comap
      (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletion)
      (fun _ hr => .of_ne_zero <| by simpa only [map_zero] using hinj.ne hr.ne_zero)
      (fun r x => Algebra.smul_def r x)
  let : Module.IsTorsionFree
      (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    IsIntegralClosure.isTorsionFree
      (w'.restrict E).adicCompletionIntegers w'.adicCompletion
  have hpne : maximalIdeal (w'.restrict E).adicCompletionIntegers ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField _
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)
  have hef :
      (maximalIdeal (w'.restrict E).adicCompletionIntegers).ramificationIdx'
          (maximalIdeal w'.adicCompletionIntegers) *
        (maximalIdeal w'.adicCompletionIntegers).inertiaDeg
          (w'.restrict E).adicCompletionIntegers =
            Module.finrank (w'.restrict E).adicCompletion w'.adicCompletion := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (maximalIdeal (w'.restrict E).adicCompletionIntegers)
      (maximalIdeal w'.adicCompletionIntegers) hpne]
    calc
      _ = ∑ q : (maximalIdeal
            (w'.restrict E).adicCompletionIntegers).primesOver
              w'.adicCompletionIntegers,
          q.1.ramificationIdx (w'.restrict E).adicCompletionIntegers *
            q.1.inertiaDeg (w'.restrict E).adicCompletionIntegers := by
              symm
              let q : (maximalIdeal
                  (w'.restrict E).adicCompletionIntegers).primesOver
                    w'.adicCompletionIntegers :=
                ⟨maximalIdeal w'.adicCompletionIntegers, by
                  rw [IsLocalRing.primesOver_eq w'.adicCompletionIntegers hpne]
                  simp⟩
              apply Finset.sum_eq_single q
              · intro b _ hb
                have : b = q := by
                  apply Subtype.ext
                  have hb : b.1 ∈ ({maximalIdeal w'.adicCompletionIntegers} :
                      Set (Ideal w'.adicCompletionIntegers)) := by
                    rw [← IsLocalRing.primesOver_eq w'.adicCompletionIntegers hpne]
                    exact b.2
                  simpa using hb
                exact (hb this).elim
              · simp
      _ = Module.finrank (w'.restrict E).adicCompletionIntegers
          w'.adicCompletionIntegers :=
            Ideal.sum_ramification_inertia_eq_finrank
              (maximalIdeal (w'.restrict E).adicCompletionIntegers)
              w'.adicCompletionIntegers
      _ = Module.finrank (w'.restrict E).adicCompletion w'.adicCompletion :=
        IsIntegralClosure.rank (w'.restrict E).adicCompletionIntegers
          (w'.restrict E).adicCompletion w'.adicCompletion w'.adicCompletionIntegers
  rw [kwF4R1V386a_ramificationIdx_completion_eq (K := K) w',
    kwF4R1V386a_inertiaDeg_completion_eq (K := K) w'] at hef
  exact_mod_cast hef.symm

end FinrankCompletionEF
section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_completionTraceSum_of_isSeparable [Algebra.IsSeparable E F] :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF
    kwF4R1V386a_distinctKernels kwF4R1V386a_finrankCompletionEF

end Headline
end KwF4R1V386a
end ModularCurve
end

noncomputable section

namespace AlgebraicCurve

section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [∀ w : Place K F, w.FiniteResidue] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]] [∀ v : Place K E, v.DCoordGenerates]
variable [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]

theorem kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS
    [HasPrincipalDivisors K F]
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F E)
    (hCTS : KwHgfV352CompletionTraceSum K F E) :
    FiberKaehlerCotraceResidueIdentity K F E := by
  intro _ _ ωE _hωE _hωF v f
  calc ∑ w ∈ v.fiber F,
          kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w
      = ∑ w' ∈ (v.fiber F).attach,
          Algebra.trace K v.ResidueField
            (kwHgfV352LocalResidueCompletion v
              (kwHgfV352CompletionTraceAt v w'.1 w'.2 f
                * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [← Finset.sum_attach (v.fiber F)
          (fun w => kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w)]
        refine Finset.sum_congr rfl fun w' _ => ?_
        rw [kaehlerResidueTerm_kaehlerPullback_diagonal_eq_dCoord_shift v w'.1 ωE f,
          hRTCC v w'.1 w'.2 (f * algebraMap E F (v.differentialCoeff ωE)),
          kwF4R1V391a_completionTraceAt_mul_algebraMap v w'.1 w'.2 f
            (v.differentialCoeff ωE)]
    _ = Algebra.trace K v.ResidueField
          (kwHgfV352LocalResidueCompletion v
            ((∑ w' ∈ (v.fiber F).attach, kwHgfV352CompletionTraceAt v w'.1 w'.2 f)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [Finset.sum_mul,
          kwHgfV352_localResidueCompletion_sum v (v.fiber F).attach _,
          map_sum]
    _ = Algebra.trace K v.ResidueField
          (kwHgfV352LocalResidueCompletion v
            (algebraMap E v.adicCompletion (Algebra.trace E F f)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [← hCTS v f]
    _ = Algebra.trace K v.ResidueField
          (v.localResidue (Algebra.trace E F f * v.differentialCoeff ωE)) := by
        rw [← map_mul, kwHgfV352_localResidueCompletion_algebraMap v]
    _ = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F f)) v := by
        unfold kaehlerResidueTerm; rw [diagonalHom_apply]

end Headline
section Compose

variable {K F : Type*} [Field K] [IsAlgClosed K]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [Nontrivial Ω[F⁄K]]

theorem kw_es_residueTheoremK_of_RTCC_isAlgClosed
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    ResidueTheoremK K F := by
  classical
  have hCTS : KwHgfV352CompletionTraceSum K F (RatFunc K) :=
    KwF4R1V386a.kwF4R1V386a_completionTraceSum_of_isSeparable (K := K) (F := F) (E := RatFunc K)
  exact residueTheoremK_of_fiberKaehlerCotraceResidueIdentity_ratFunc_isAlgClosed hgen
    (kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS hRTCC hCTS)

theorem kw_es_residueTheoremK_of_RTCC_isAlgClosed'
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    ResidueTheoremK K F := by
  classical
  exact
    kw_es_residueTheoremK_of_RTCC_isAlgClosed
      (kaehlerPullback_eq_kaehlerCotrace (K := K) (F := F) (E := RatFunc K) (dX K) ▸
        kaehlerCotrace_dX_ne_zero_of_isSeparable K F (RationalFunctionField.placeInfty K))
      hRTCC

end Compose
end AlgebraicCurve
end
section S18AliasSR
open scoped ModularCurve in
theorem ModularCurve.KwTateRR3.kwTateRR3_RTCC_of_isSeparable
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [∀ u : AlgebraicCurve.Place K E, u.FiniteResidue]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K E] [PerfectField K]
    [Nontrivial Ω[F⁄K]]
    [Algebra.IsSeparable E F] :
    ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F E :=
  AlgebraicCurve.residueTraceCompletionCommute
end S18AliasSR
section

open LinearMap Submodule
open ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve
namespace KwTateRR3

section RTKCapstone

variable {K F : Type*} [Field K] [IsAlgClosed K]
variable [Field F] [Algebra K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [Nontrivial Ω[F⁄K]]
variable [IsCurveOver K F]
variable [∀ u : Place K (RatFunc K), u.FiniteResidue]

theorem kwTateRR3_residueTheoremK_of_isAlgClosed
    [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates] :
    ResidueTheoremK K F := by
  classical
  exact
    kw_es_residueTheoremK_of_RTCC_isAlgClosed'
      (kwTateRR3_RTCC_of_isSeparable (E := RatFunc K))

end RTKCapstone
end KwTateRR3
end ModularCurve
end
end
theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K F := by
  classical
  exact
    ModularCurve.KwTateRR3.kwTateRR3_residueTheoremK_of_isAlgClosed

end

end privateSection

public section publicSection

theorem AlgebraicCurve.residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K F := by
  classical
  exact
    solution

end publicSection
