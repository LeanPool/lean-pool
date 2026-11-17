/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

/-
Adapted from the Prove2Me proofs by Claude (2026-09-05) of
AlgebraicCurve.Place.ord_diffCoeff_D_nonneg (submission
be1faaa5-7f5b-53d4-80a6-b4a470ea647b) and
AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable (submission
5db19e19-28c2-5a1b-a164-633c1970ef3c).
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_DivisorClassGroup

import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Regular derivatives with respect to a uniformizer

Over a perfect constant field, let `F` be finite and separable over `K(t)`. At a place
where `t` has order one, every regular function `f` satisfies `df = g • dt` with `g`
regular. The proof realizes the valuation ring as an essentially finite-type unramified
algebra over the polynomial parameter, then uses the exact sequence of differentials.

Only `AlgebraicCurve.Place.exists_regular_derivative` is exported; the rational-function
presentation and all local-ring machinery are private.
-/

noncomputable section

open IsDedekindDomain WithZero IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace AlgebraicCurve

open Place

section privateSection

theorem polyMem {K : Type*} [Field K] (u : Place K (RatFunc K))
    (hX : (RatFunc.X : RatFunc K) ∈ u.toValuationSubring) (p : Polynomial K) :
    algebraMap (Polynomial K) (RatFunc K) p ∈ u.toValuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    refine mul_mem ?_ (pow_mem ?_ n)
    · rw [← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
      exact u.algebraMap_mem' a
    · rw [RatFunc.algebraMap_X]
      exact hX

theorem isLocalization_valuationSubring {K Φ : Type*} [Field K] [Field Φ] [Algebra K Φ]
    (w : Place K Φ) {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R Φ]
    [IsFractionRing R Φ] (P : HeightOneSpectrum R) [Algebra R w.toValuationSubring]
    (halg : ∀ r : R, (algebraMap R w.toValuationSubring r : Φ) = algebraMap R Φ r)
    (heq : w.toValuationSubring = HeightOneSpectrum.valuationSubringAtPrime Φ P)
    (hmem : ∀ {r : R}, r ≠ 0 → (r ∈ P.asIdeal ↔ 0 < w.ord (algebraMap R Φ r))) :
    IsLocalization P.asIdeal.primeCompl w.toValuationSubring := by
  refine (isLocalization_iff P.asIdeal.primeCompl w.toValuationSubring).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := fun h => hs (h ▸ P.asIdeal.zero_mem)
    have hsΦ : algebraMap R Φ s ≠ 0 := fun h =>
      hs0 (IsFractionRing.injective R Φ (by rw [h, map_zero]))
    have hordle : ¬ 0 < w.ord (algebraMap R Φ s) := fun h => hs ((hmem hs0).mpr h)
    have hmem' : algebraMap R Φ s ∈ w.toValuationSubring :=
      halg s ▸ (algebraMap R w.toValuationSubring s).2
    have hordge : 0 ≤ w.ord (algebraMap R Φ s) := w.ord_nonneg_of_mem hmem'
    have hord0 : w.ord (algebraMap R Φ s) = 0 := by omega
    have hinv : (algebraMap R Φ s)⁻¹ ∈ w.toValuationSubring :=
      w.mem_of_ord_nonneg (inv_ne_zero hsΦ) (by rw [w.ord_inv, hord0]; omega)
    refine isUnit_iff_exists_inv.mpr ⟨⟨(algebraMap R Φ s)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    change (algebraMap R w.toValuationSubring s : Φ) * (algebraMap R Φ s)⁻¹ = 1
    rw [halg, mul_inv_cancel₀ hsΦ]
  · intro z
    have hz : (z : Φ) ∈ HeightOneSpectrum.valuationSubringAtPrime Φ P := heq ▸ z.2
    obtain ⟨⟨a, s⟩, hfrac⟩ := IsLocalization.surj
      (S := HeightOneSpectrum.valuationSubringAtPrime Φ P) P.asIdeal.primeCompl ⟨(z : Φ), hz⟩
    have hWcoe : ∀ r : R,
        (algebraMap R (HeightOneSpectrum.valuationSubringAtPrime Φ P) r : Φ)
          = algebraMap R Φ r := fun r => by
      rw [IsScalarTower.algebraMap_apply R (HeightOneSpectrum.valuationSubringAtPrime Φ P) Φ]
      rfl
    have hfrac' := congrArg
      (Subtype.val : (HeightOneSpectrum.valuationSubringAtPrime Φ P) → Φ) hfrac
    refine ⟨⟨a, s⟩, ?_⟩
    apply Subtype.ext
    change (z : Φ) * (algebraMap R w.toValuationSubring (s : R) : Φ)
      = (algebraMap R w.toValuationSubring a : Φ)
    rw [halg, halg, ← hWcoe (s : R), ← hWcoe a]
    exact hfrac'
  · intro a b h
    have hΦ : algebraMap R Φ a = algebraMap R Φ b := by
      rw [← halg a, ← halg b]
      exact congrArg (Subtype.val : w.toValuationSubring → Φ) h
    exact ⟨1, by rw [IsFractionRing.injective R Φ hΦ]⟩

theorem isAlgebraic_residue {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    {x : S} (hx : ∃ p : Polynomial R, p.Monic ∧ Polynomial.eval₂ (algebraMap R S) x p = 0) :
    IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.residue S x) := by
  obtain ⟨p, hpm, hpe⟩ := hx
  refine ⟨p.map (IsLocalRing.residue R), (hpm.map _).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have hcomp : (algebraMap (ResidueField R) (ResidueField S)).comp (IsLocalRing.residue R)
      = (IsLocalRing.residue S).comp (algebraMap R S) :=
    RingHom.ext fun r => IsLocalRing.ResidueField.algebraMap_residue r
  rw [hcomp, ← Polynomial.hom_eval₂, hpe, map_zero]

theorem isAlgebraic_residueField_of_X_mem {K : Type*} [Field K] (u : Place K (RatFunc K))
    [Algebra (Polynomial K) u.toValuationSubring]
    (halg : ∀ p : Polynomial K, (algebraMap (Polynomial K) u.toValuationSubring p : RatFunc K)
      = algebraMap (Polynomial K) (RatFunc K) p)
    (S : Submonoid (Polynomial K)) [IsLocalization S u.toValuationSubring]
    (hX : algebraMap (Polynomial K) u.toValuationSubring Polynomial.X
      ∈ IsLocalRing.maximalIdeal u.toValuationSubring) :
    Algebra.IsAlgebraic K (IsLocalRing.ResidueField u.toValuationSubring) := by
  have hC : ∀ c : K, algebraMap (Polynomial K) u.toValuationSubring (Polynomial.C c)
      = algebraMap K u.toValuationSubring c := by
    intro c
    apply Subtype.ext
    rw [halg, Place.coe_algebraMap, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
  have hres : ∀ p : Polynomial K,
      IsLocalRing.residue u.toValuationSubring (algebraMap (Polynomial K) u.toValuationSubring p)
        = algebraMap K (IsLocalRing.ResidueField u.toValuationSubring) (p.coeff 0) := by
    intro p
    rw [IsScalarTower.algebraMap_apply K u.toValuationSubring
        (IsLocalRing.ResidueField u.toValuationSubring),
      IsLocalRing.ResidueField.algebraMap_eq, ← hC, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← map_sub]
    have hp : p - Polynomial.C (p.coeff 0) = Polynomial.X * p.divX := by
      rw [sub_eq_iff_eq_add, Polynomial.X_mul_divX_add]
    rw [hp, map_mul]
    exact Ideal.mul_mem_right _ _ hX
  constructor
  intro y
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj S z
  have hsu : IsUnit (algebraMap (Polynomial K) u.toValuationSubring (s : Polynomial K)) :=
    IsLocalization.map_units u.toValuationSubring s
  have hs0 : algebraMap K (IsLocalRing.ResidueField u.toValuationSubring)
      ((s : Polynomial K).coeff 0) ≠ 0 := by
    rw [← hres]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hsu
  have hz : IsLocalRing.residue u.toValuationSubring z
      = algebraMap K (IsLocalRing.ResidueField u.toValuationSubring)
          (a.coeff 0 / (s : Polynomial K).coeff 0) := by
    have h' := congrArg (IsLocalRing.residue u.toValuationSubring) h
    rw [map_mul, hres, hres] at h'
    rw [map_div₀, eq_div_iff hs0, h']
  rw [hz]
  exact isAlgebraic_algebraMap _

section Dict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable {v : Place K F} {w : Place K F'}

def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  (algebraMap (integralClosureAt F' v) F').codRestrict
    w.toValuationSubring.toSubring (forall_mem_of_restrict_eq hw)

def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  (IsLocalRing.residue w.toValuationSubring).comp (toValuationSubringOfRestrictEq hw)

omit [FiniteDimensional F F'] in
theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) := rfl

theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : F') ∈ HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) := by
    rw [← toValuationSubring_eq_of_restrict_eq hw]
    exact x.2
  obtain ⟨a, s, hs, hxas⟩ := hx
  have hsP : s ∉ (fiberCenter F' v hw).asIdeal := hs
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ (fiberCenter F' v hw).asIdeal.zero_mem)
  have hsF : algebraMap (integralClosureAt F' v) F' s ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hs0
  have hsord : w.ord (algebraMap (integralClosureAt F' v) F' s) = 0 := by
    have h1 : ¬ 0 < w.ord (algebraMap (integralClosureAt F' v) F' s) := by
      rw [← mem_fiberCenter_iff_ord_pos hw hs0]
      exact hsP
    have h2 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' s) :=
      w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw s)
    omega
  have hmax : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv hsP
  have hst : s * t - 1 ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : s * t - 1 = -i := by linear_combination hti
    rw [h1]
    exact neg_mem hi
  refine ⟨a * t, ?_⟩
  rw [residueOfCenter_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hcoe : ((toValuationSubringOfRestrictEq hw (a * t) - x : w.toValuationSubring) : F')
      = algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') := rfl
  rcases eq_or_ne (toValuationSubringOfRestrictEq hw (a * t) - x) 0 with hzero | hne
  · rw [hzero]
    exact (IsLocalRing.maximalIdeal w.toValuationSubring).zero_mem
  have hcoene : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') ≠ 0 := by
    intro h
    exact hne (by rwa [← hcoe, ZeroMemClass.coe_eq_zero] at h)
  have hfactor : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      = algebraMap (integralClosureAt F' v) F' (a * t * s - a)
          * (algebraMap (integralClosureAt F' v) F' s)⁻¹ := by
    rw [hxas, map_sub, map_mul (algebraMap (integralClosureAt F' v) F') (a * t) s,
      sub_mul, mul_assoc, mul_inv_cancel₀ hsF, mul_one]
  have hdiffC : a * t * s - a ≠ 0 := by
    intro h
    apply hcoene
    rw [hfactor, h, map_zero, zero_mul]
  have hdiffP : a * t * s - a ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : a * t * s - a = a * (s * t - 1) := by ring
    rw [h1]
    exact Ideal.mul_mem_left _ _ hst
  have hmem' : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      ∈ w.toValuationSubring := by
    rw [← hcoe]
    exact Subtype.coe_prop _
  rw [show (toValuationSubringOfRestrictEq hw (a * t) - x)
      = (⟨_, hmem'⟩ : w.toValuationSubring) from Subtype.ext hcoe,
    w.mem_maximalIdeal_iff_ord_pos hcoene hmem']
  rw [hfactor, w.ord_mul (by
      simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hdiffC)
    (inv_ne_zero hsF), w.ord_inv, hsord, neg_zero, add_zero]
  exact (mem_fiberCenter_iff_ord_pos hw hdiffC).mp hdiffP

end Dict

/-- Formal unramifiedness over the polynomial parameter makes the derivative of a
regular function a regular multiple of the parameter's differential. -/
theorem exists_regular_derivative_of_formallyUnramified
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    [Algebra (Polynomial K) v.toValuationSubring]
    [IsScalarTower K (Polynomial K) v.toValuationSubring]
    [Algebra.FormallyUnramified (Polynomial K) v.toValuationSubring]
    {t : F} (ht : algebraMap v.toValuationSubring F
      (algebraMap (Polynomial K) v.toValuationSubring Polynomial.X) = t)
    {f : F} (hf : 0 ≤ v.ord f) :
    ∃ g : F, 0 ≤ v.ord g ∧ D K F f = g • D K F t := by
  have hspan : ∀ ω : Ω[↥v.toValuationSubring⁄K], ω ∈ Submodule.span v.toValuationSubring
      {D K v.toValuationSubring (algebraMap (Polynomial K) v.toValuationSubring
        Polynomial.X)} := by
    intro ω
    have hexact := KaehlerDifferential.exact_mapBaseChange_map K (Polynomial K)
      v.toValuationSubring
    have h0 : KaehlerDifferential.map K (Polynomial K) v.toValuationSubring
        v.toValuationSubring ω = 0 := Subsingleton.elim _ _
    obtain ⟨ξ, hξ⟩ := (hexact ω).mp h0
    rw [← hξ]
    clear hξ
    induction ξ using TensorProduct.inductionOn with
    | tmul b ω' =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      have hω' : ω' = ((KaehlerDifferential.polynomialEquiv K) ω')
          • D K (Polynomial K) Polynomial.X :=
        ((KaehlerDifferential.polynomialEquiv K).symm_apply_apply ω').symm
      rw [hω', map_smul, KaehlerDifferential.map_D]
      rw [show ((KaehlerDifferential.polynomialEquiv K) ω') • D K v.toValuationSubring
          (algebraMap (Polynomial K) v.toValuationSubring Polynomial.X)
        = (algebraMap (Polynomial K) v.toValuationSubring
            ((KaehlerDifferential.polynomialEquiv K) ω'))
            • D K v.toValuationSubring (algebraMap (Polynomial K) v.toValuationSubring
              Polynomial.X)
        from (algebraMap_smul _ _ _).symm, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | add ξ₁ ξ₂ h₁ h₂ =>
      rw [map_add]
      exact Submodule.add_mem _ h₁ h₂
  have hfmem : f ∈ v.toValuationSubring := by
    rcases eq_or_ne f 0 with rfl | hf0
    · exact zero_mem _
    · exact v.mem_of_ord_nonneg hf0 hf
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp
    (hspan (D K v.toValuationSubring ⟨f, hfmem⟩))
  have hpush := congrArg (KaehlerDifferential.map K K v.toValuationSubring F) hg
  rw [map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at hpush
  have hfOvF : algebraMap v.toValuationSubring F (⟨f, hfmem⟩ : v.toValuationSubring) = f := rfl
  rw [ht, hfOvF] at hpush
  have hgsmul : ((g : F)) • D K F t
      = g • D K F t := algebraMap_smul F g _
  rw [← hgsmul] at hpush
  exact ⟨g, v.ord_nonneg_of_mem g.2, hpush.symm⟩

theorem exists_regular_derivative_ratFunc {K : Type*} [Field K] [PerfectField K]
    {F : Type*} [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F]
    (v : Place K F) {u : Place K (RatFunc K)} (hu : Place.restrict (RatFunc K) v = u)
    (ht : v.ord (algebraMap (RatFunc K) F RatFunc.X) = 1)
    {f : F} (hf : 0 ≤ v.ord f) :
    ∃ g : F, 0 ≤ v.ord g ∧ D K F f = g • D K F (algebraMap (RatFunc K) F RatFunc.X) := by
  classical
  have : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite _ _
  have hepos : 0 < v.ramificationIndex (RatFunc K) := v.ramificationIndex_pos
  have hres : v.ord (algebraMap (RatFunc K) F RatFunc.X)
      = (v.ramificationIndex (RatFunc K) : ℤ)
        * (Place.restrict (RatFunc K) v).ord RatFunc.X :=
    v.ord_restrict RatFunc.X
  rw [hu, ht] at hres
  have huX : u.ord RatFunc.X = 1 := by
    have hdvd : ((v.ramificationIndex (RatFunc K) : ℤ)) ∣ 1 := ⟨u.ord RatFunc.X, hres⟩
    have hle := Int.le_of_dvd one_pos hdvd
    have he1 : v.ramificationIndex (RatFunc K) = 1 := by omega
    rw [he1] at hres
    omega
  have hX0 : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hXmem : (RatFunc.X : RatFunc K) ∈ u.toValuationSubring :=
    u.mem_of_ord_nonneg hX0 (by rw [huX]; omega)
  have htne : algebraMap (RatFunc K) F RatFunc.X ≠ 0 := by
    intro h
    rw [h, Place.ord_zero] at ht
    exact zero_ne_one ht
  let instCOv : Algebra (integralClosureAt F u) v.toValuationSubring :=
    (toValuationSubringOfRestrictEq hu).toAlgebra
  have halgC : ∀ c : integralClosureAt F u,
      (algebraMap (integralClosureAt F u) v.toValuationSubring c : F)
        = algebraMap (integralClosureAt F u) F c := fun _ => rfl
  have hloc : IsLocalization (fiberCenter F u hu).asIdeal.primeCompl v.toValuationSubring :=
    isLocalization_valuationSubring v (fiberCenter F u hu) halgC
      (toValuationSubring_eq_of_restrict_eq hu)
      (fun {c} hc => mem_fiberCenter_iff_ord_pos hu hc)
  let instOuOv : Algebra u.toValuationSubring v.toValuationSubring :=
    ((algebraMap (integralClosureAt F u) v.toValuationSubring).comp
      (algebraMap u.toValuationSubring (integralClosureAt F u))).toAlgebra
  have instTowOuCOv : IsScalarTower u.toValuationSubring (integralClosureAt F u)
      v.toValuationSubring := IsScalarTower.of_algebraMap_eq' rfl
  have halgOuOv : ∀ g : u.toValuationSubring,
      (algebraMap u.toValuationSubring v.toValuationSubring g : F)
        = algebraMap (RatFunc K) F (g : RatFunc K) := by
    intro g
    change (algebraMap (integralClosureAt F u) v.toValuationSubring
      (algebraMap u.toValuationSubring (integralClosureAt F u) g) : F) = _
    rw [halgC, ← IsScalarTower.algebraMap_apply u.toValuationSubring (integralClosureAt F u) F,
      IsScalarTower.algebraMap_apply u.toValuationSubring (RatFunc K) F]
    rfl
  have hcompOuF : (algebraMap v.toValuationSubring F).comp
      (algebraMap u.toValuationSubring v.toValuationSubring)
        = algebraMap u.toValuationSubring F := by
    apply RingHom.ext
    intro g
    change (algebraMap u.toValuationSubring v.toValuationSubring g : F) = _
    rw [halgOuOv g, IsScalarTower.algebraMap_apply u.toValuationSubring (RatFunc K) F]
    rfl
  have instEFT : Algebra.EssFiniteType u.toValuationSubring v.toValuationSubring := by
    have h2 : Algebra.EssFiniteType (integralClosureAt F u) v.toValuationSubring :=
      Algebra.EssFiniteType.of_isLocalization _ (fiberCenter F u hu).asIdeal.primeCompl
    exact Algebra.EssFiniteType.comp u.toValuationSubring (integralClosureAt F u)
      v.toValuationSubring
  have instLH : IsLocalHom (algebraMap u.toValuationSubring v.toValuationSubring) := by
    constructor
    intro a ha
    by_contra hnu
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact not_isUnit_zero ha
    have hposu : 0 < u.ord (algebraMap u.toValuationSubring (RatFunc K) a) :=
      (Place.mem_maximalIdeal_iff_ord_pos' ha0).mp ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have himg0 : v.ord ((algebraMap u.toValuationSubring v.toValuationSubring a : F)) = 0 := by
      have h := v.ord_coe_unit ha.unit
      rwa [ha.unit_spec] at h
    have himgpos : 0 < v.ord ((algebraMap u.toValuationSubring v.toValuationSubring a : F)) := by
      rw [halgOuOv a, v.ord_restrict, hu]
      exact mul_pos (by exact_mod_cast hepos) hposu
    omega
  have hpmem : ∀ p : Polynomial K,
      algebraMap (Polynomial K) (RatFunc K) p ∈ u.toValuationSubring := polyMem u hXmem
  let instKXOu : Algebra (Polynomial K) u.toValuationSubring :=
    ((algebraMap (Polynomial K) (RatFunc K)).codRestrict
      u.toValuationSubring.toSubring hpmem).toAlgebra
  have halgKXOu : ∀ p : Polynomial K,
      (algebraMap (Polynomial K) u.toValuationSubring p : RatFunc K)
        = algebraMap (Polynomial K) (RatFunc K) p := fun _ => rfl
  have hlocKX : IsLocalization
      (centerHeightOneSpectrum (Polynomial K) u hpmem).asIdeal.primeCompl
        u.toValuationSubring :=
    isLocalization_valuationSubring u (centerHeightOneSpectrum (Polynomial K) u hpmem) halgKXOu
      (toValuationSubring_eq_of_forall_mem u hpmem)
      (fun {r} hr => by
        rw [centerHeightOneSpectrum_asIdeal]
        exact mem_center_iff_ord_pos u hpmem hr)
  have hXune : (⟨RatFunc.X, hXmem⟩ : u.toValuationSubring) ≠ 0 := by
    intro h
    exact hX0 (by simpa using congrArg Subtype.val h)
  have hXu_mm : (⟨RatFunc.X, hXmem⟩ : u.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal u.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_ord_pos' hXune]
    show 0 < u.ord (algebraMap u.toValuationSubring (RatFunc K) ⟨RatFunc.X, hXmem⟩)
    have hX : algebraMap u.toValuationSubring (RatFunc K) ⟨RatFunc.X, hXmem⟩
        = RatFunc.X := rfl
    rw [hX, huX]
    omega
  have hXKX_mm : algebraMap (Polynomial K) u.toValuationSubring Polynomial.X
      ∈ IsLocalRing.maximalIdeal u.toValuationSubring := by
    have h1 : algebraMap (Polynomial K) u.toValuationSubring Polynomial.X
        = ⟨RatFunc.X, hXmem⟩ := Subtype.ext (by rw [halgKXOu, RatFunc.algebraMap_X])
    rw [h1]
    exact hXu_mm
  have instAκu : Algebra.IsAlgebraic K (IsLocalRing.ResidueField u.toValuationSubring) :=
    isAlgebraic_residueField_of_X_mem u halgKXOu
      (centerHeightOneSpectrum (Polynomial K) u hpmem).asIdeal.primeCompl hXKX_mm
  have instPFκu : PerfectField (IsLocalRing.ResidueField u.toValuationSubring) :=
    Algebra.IsAlgebraic.perfectField (K := K)
  have instAκ : Algebra.IsAlgebraic (IsLocalRing.ResidueField u.toValuationSubring)
      (IsLocalRing.ResidueField v.toValuationSubring) := by
    constructor
    intro y
    obtain ⟨c, hc⟩ := surjective_residueOfCenter hu y
    rw [← hc, residueOfCenter_apply]
    apply isAlgebraic_residue
    obtain ⟨p, hpm, hpe⟩ := c.2
    refine ⟨p, hpm, ?_⟩
    have hinj : Function.Injective (algebraMap v.toValuationSubring F) :=
      IsFractionRing.injective _ _
    apply hinj
    rw [map_zero, Polynomial.hom_eval₂, hcompOuF]
    exact hpe
  have hmapmax : Ideal.map (algebraMap u.toValuationSubring v.toValuationSubring)
      (IsLocalRing.maximalIdeal u.toValuationSubring)
        = IsLocalRing.maximalIdeal v.toValuationSubring := by
    apply le_antisymm
    · exact ((IsLocalRing.local_hom_TFAE
        (algebraMap u.toValuationSubring v.toValuationSubring)).out 1 3).mp instLH
    · intro z hz
      rcases eq_or_ne z 0 with rfl | hz0
      · exact zero_mem _
      have hposz : 0 < v.ord (algebraMap v.toValuationSubring F z) :=
        (Place.mem_maximalIdeal_iff_ord_pos' hz0).mp hz
      have hzF : (z : F) ≠ 0 := fun h => hz0 (ZeroMemClass.coe_eq_zero.mp h)
      have hyne : (z : F) * (algebraMap (RatFunc K) F RatFunc.X)⁻¹ ≠ 0 :=
        mul_ne_zero hzF (inv_ne_zero htne)
      have hyord : 0 ≤ v.ord ((z : F) * (algebraMap (RatFunc K) F RatFunc.X)⁻¹) := by
        rw [v.ord_mul hzF (inv_ne_zero htne), v.ord_inv, ht]
        have hposz' : 0 < v.ord (z : F) := hposz
        omega
      have hymem : (z : F) * (algebraMap (RatFunc K) F RatFunc.X)⁻¹ ∈ v.toValuationSubring :=
        v.mem_of_ord_nonneg hyne hyord
      have hfact : z = algebraMap u.toValuationSubring v.toValuationSubring ⟨RatFunc.X, hXmem⟩
          * ⟨(z : F) * (algebraMap (RatFunc K) F RatFunc.X)⁻¹, hymem⟩ := by
        apply Subtype.ext
        change (z : F) = (algebraMap u.toValuationSubring v.toValuationSubring
          ⟨RatFunc.X, hXmem⟩ : F) * ((z : F) * (algebraMap (RatFunc K) F RatFunc.X)⁻¹)
        rw [halgOuOv]
        change (z : F) = algebraMap (RatFunc K) F RatFunc.X
          * ((z : F) * (algebraMap (RatFunc K) F RatFunc.X)⁻¹)
        rw [mul_comm (z : F) _, ← mul_assoc, mul_inv_cancel₀ htne, one_mul]
      rw [hfact]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hXu_mm)
  have hFU1 : Algebra.FormallyUnramified u.toValuationSubring v.toValuationSubring :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmapmax
  have hFU0 : Algebra.FormallyUnramified (Polynomial K) u.toValuationSubring :=
    Algebra.FormallyUnramified.of_isLocalization
      (centerHeightOneSpectrum (Polynomial K) u hpmem).asIdeal.primeCompl
  let instKXOv : Algebra (Polynomial K) v.toValuationSubring :=
    ((algebraMap u.toValuationSubring v.toValuationSubring).comp
      (algebraMap (Polynomial K) u.toValuationSubring)).toAlgebra
  have instTowKXOuOv : IsScalarTower (Polynomial K) u.toValuationSubring
      v.toValuationSubring := IsScalarTower.of_algebraMap_eq' rfl
  have hFU : Algebra.FormallyUnramified (Polynomial K) v.toValuationSubring :=
    Algebra.FormallyUnramified.comp (Polynomial K) u.toValuationSubring v.toValuationSubring
  have instTowKKXOv : IsScalarTower K (Polynomial K) v.toValuationSubring := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    apply Subtype.ext
    rw [Place.coe_algebraMap]
    change algebraMap K F a = (algebraMap u.toValuationSubring v.toValuationSubring
      (algebraMap (Polynomial K) u.toValuationSubring (algebraMap K (Polynomial K) a)) : F)
    rw [halgOuOv, halgKXOu, ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply K (RatFunc K) F]
  have hXOvF : algebraMap v.toValuationSubring F
      (algebraMap (Polynomial K) v.toValuationSubring Polynomial.X)
        = algebraMap (RatFunc K) F RatFunc.X := by
    change (algebraMap u.toValuationSubring v.toValuationSubring
      (algebraMap (Polynomial K) u.toValuationSubring Polynomial.X) : F) = _
    rw [halgOuOv, halgKXOu, RatFunc.algebraMap_X]
  exact exists_regular_derivative_of_formallyUnramified v hXOvF hf

end privateSection

public section publicSection

/-- A function regular at a place has a regular derivative with respect to any
uniformizer `t`, provided `F/K(t)` is finite and separable and `K` is perfect. -/
theorem Place.exists_regular_derivative {K F : Type*} [Field K] [Field F]
    [Algebra K F] [PerfectField K] (v : Place K F) {t : F}
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F]
    (ht : v.ord t = 1) {f : F} (hf : 0 ≤ v.ord f) :
    ∃ g : F, 0 ≤ v.ord g ∧ D K F f = g • D K F t := by
  classical
  have htr : Transcendental K t :=
    v.transcendental_of_ord_ne_zero (by rw [ht]; exact one_ne_zero)
  let e : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K ({t} : Set F)) :=
    RatFunc.algEquivOfTranscendental t htr
  let : Algebra (RatFunc K) (↥(IntermediateField.adjoin K ({t} : Set F))) :=
    e.toAlgHom.toRingHom.toAlgebra
  let : Algebra (RatFunc K) F :=
    ((algebraMap (↥(IntermediateField.adjoin K ({t} : Set F))) F).comp
      e.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower (RatFunc K) (↥(IntermediateField.adjoin K ({t} : Set F))) F :=
    IsScalarTower.of_algebraMap_eq fun q => rfl
  have : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap K F r
      = algebraMap (↥(IntermediateField.adjoin K ({t} : Set F))) F (e (algebraMap K (RatFunc K) r))
    rw [AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply K (↥(IntermediateField.adjoin K ({t} : Set F))) F r
  have : Module.Finite (RatFunc K) (↥(IntermediateField.adjoin K ({t} : Set F))) :=
    Module.Finite.of_surjective
      (Algebra.linearMap (RatFunc K) (↥(IntermediateField.adjoin K ({t} : Set F))))
      e.surjective
  have : FiniteDimensional (RatFunc K) F :=
    Module.Finite.trans (↥(IntermediateField.adjoin K ({t} : Set F))) F
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun y => by
        change algebraMap (↥(IntermediateField.adjoin K ({t} : Set F))) F (e (e.symm y))
          = algebraMap (↥(IntermediateField.adjoin K ({t} : Set F))) F y
        rw [AlgEquiv.apply_symm_apply])
  have hXt : algebraMap (RatFunc K) F RatFunc.X = t :=
    RatFunc.algEquivOfTranscendental_X t htr
  have ht' : v.ord (algebraMap (RatFunc K) F RatFunc.X) = 1 := by rw [hXt]; exact ht
  obtain ⟨g, hg, hDf⟩ := exists_regular_derivative_ratFunc v rfl ht' hf
  exact ⟨g, hg, by simpa only [hXt] using hDf⟩

end publicSection

end AlgebraicCurve
