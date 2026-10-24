/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

/-
Extracted from Prove2Me proofs by Claude (2026-09-05):
* isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
  (f4d949d7-d2e9-583c-970a-d2c81be54545), submission
  dc1eabf7-1867-53e3-b324-7414996a1c99.
* exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
  (e43a54a4-70bb-5551-8efe-0ba1b5eb4b2c), submission
  3e4feffd-4b48-5cc6-aa05-ac80b8acf609.
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Defs_IsogenyEndDatum_sharedLibrary

import Mathlib.Algebra.Algebra.Field
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum.Prime
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Base change of finite elliptic-curve function-field maps

The sole public theorem constructs a base-changed map, preserves its degree, and proves
compatibility with scalar extension both on function fields and on points. Tensor-product,
valuation-ring and point-naturality constructions are private implementation details.
-/

noncomputable section

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine Polynomial AlgebraicCurve
open scoped TensorProduct Polynomial Polynomial.Bivariate

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable

/-- The local ring at an affine point consists of fractions with denominator
nonvanishing at that point. -/
theorem mem_placeOfEquation_iff_fraction {K : Type*} [Field K] (W : Affine K)
    [IsDedekindDomain W.CoordinateRing]
    {x y : K} (hP : W.Nonsingular x y) : ∀ f : W.FunctionField,
    f ∈ (placeOfEquation hP.left).toValuationSubring
      ↔ ∃ (n s : W.CoordinateRing)
          (_ : s ∉ CoordinateRing.XYIdeal W x (C y)),
        f = algebraMap _ _ n * (algebraMap _ _ s)⁻¹ := by
  intro f
  have : (CoordinateRing.XYIdeal W x (C y)).IsPrime :=
    (CoordinateRing.XYIdeal_isMaximal hP.left).isPrime
  have hfinP := isFinitePlace_placeOfEquation hP.left
  constructor
  · intro hf
    obtain ⟨n, s, hcase⟩ :=
      (CoordinateRing.heightOneSpectrumOfEquation hP.left).exists_primeCompl_mul_eq_or_mul_eq
        (K := W.FunctionField) f
    have hs_nin : (s : W.CoordinateRing)
        ∉ CoordinateRing.XYIdeal W x (C y) :=
      Ideal.mem_primeCompl_iff.mp s.2
    have hs_CR_ne : (s : W.CoordinateRing) ≠ 0 :=
      fun h => hs_nin (h ▸ Ideal.zero_mem _)
    have hs0 : algebraMap W.CoordinateRing
        W.FunctionField (s : W.CoordinateRing) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs_CR_ne
    rcases hcase with heq | heq
    · refine ⟨n, s, hs_nin, ?_⟩
      field_simp at heq ⊢; linear_combination heq
    · by_cases hn_nin : (n : _) ∈ CoordinateRing.XYIdeal W x (C y)
      · exfalso
        have hn0 : (n : W.CoordinateRing) ≠ 0 := fun h => by
          rw [h, map_zero, mul_zero] at heq
          exact hs_CR_ne ((map_eq_zero_iff _
            (IsFractionRing.injective _ _)).mp heq.symm)
        have hord_n_pos : 0 < (placeOfEquation hP.left).ord (algebraMap _ _ (n : _)) :=
          (ord_placeOfEquation_pos_iff hP.left hn0).mpr hn_nin
        have hord_s_zero : (placeOfEquation hP.left).ord
            (algebraMap _ _ (s : W.CoordinateRing)) = 0 := by
          by_contra hne
          exact hs_nin ((ord_placeOfEquation_ne_zero_iff hP.left hs_CR_ne).mp hne)
        have hord_f_neg : (placeOfEquation hP.left).ord f < 0 := by
          have hf0 : f ≠ 0 := fun h => by
            rw [h, zero_mul] at heq
            exact hs_CR_ne ((map_eq_zero_iff _
              (IsFractionRing.injective _ _)).mp heq.symm)
          have hfn_eq : (placeOfEquation hP.left).ord f
              + (placeOfEquation hP.left).ord (algebraMap _ _ (n : _))
              = (placeOfEquation hP.left).ord
                  (algebraMap _ _ (s : W.CoordinateRing)) := by
            rw [← Place.ord_mul _ hf0
                ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hn0), heq]
          omega
        exact not_le.mpr hord_f_neg (AlgebraicCurve.Place.ord_nonneg_of_mem (placeOfEquation
          hP.left) hf)
      · refine ⟨s, n, hn_nin, ?_⟩
        have hn0 : algebraMap _ W.FunctionField (n : _) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
            (fun h => hn_nin (h ▸ Ideal.zero_mem _))
        field_simp at heq ⊢; linear_combination heq
  · rintro ⟨n, s, hs_nin, rfl⟩
    have hs_inv : (algebraMap _ _ s)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
      hfinP.inv_mem (by rwa [centre_placeOfEquation])
    exact Subring.mul_mem _ (hfinP n) hs_inv

section BetweenCurvesTensor

variable {R₀ : Type u} [Field R₀]
variable (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']
variable [(E₀⁄F).IsElliptic] [(E₀⁄F).toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (E₀⁄F).toAffine]
    [(E₀⁄F).toAffine.AbelTheorem] [(E₀'⁄F).IsElliptic]
    [(E₀'⁄F).toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (E₀'⁄F).toAffine]
    [(E₀'⁄F).toAffine.AbelTheorem] [(E₀⁄F').IsElliptic]
    [(E₀⁄F').toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (E₀⁄F').toAffine]
    [(E₀⁄F').toAffine.AbelTheorem] [(E₀'⁄F').IsElliptic]
    [(E₀'⁄F').toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (E₀'⁄F').toAffine]
    [(E₀'⁄F').toAffine.AbelTheorem]
variable (ι₀ : (E₀'⁄F).toAffine.FunctionField →ₐ[F] (E₀⁄F).toAffine.FunctionField)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def kw_surge_hgf4_bcTensorIota :
    (E₀'⁄F).toAffine.FunctionField ⊗[F] F' →ₐ[F] (E₀⁄F).toAffine.FunctionField ⊗[F] F' :=
  Algebra.TensorProduct.map ι₀ (AlgHom.id F F')

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcTensorIota_tmul (a : (E₀'⁄F).toAffine.FunctionField) (c : F') :
    kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀ (a ⊗ₜ[F] c) = (ι₀ a) ⊗ₜ[F] c := by
  simp [kw_surge_hgf4_bcTensorIota, Algebra.TensorProduct.map_tmul]

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcTensorIota_injective :
    Function.Injective (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := F') ι₀.toLinearMap ι₀.injective

variable [IsDomain ((E₀⁄F).toAffine.FunctionField ⊗[F] F')]
variable [IsDomain ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')]

def kw_surge_hgf4_bcTensorFracIota :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →+* FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
    (L := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))
    (kw_surge_hgf4_bcTensorIota_injective E₀ E₀' F F' ι₀)

omit [IsDomain ((toAffine E₀'⁄F).FunctionField ⊗[F] F')] in
omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcTensorFracIota_algebraMap
    (t : (E₀'⁄F).toAffine.FunctionField ⊗[F] F') :
    kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ t)
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
          (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀ t) := by
  unfold kw_surge_hgf4_bcTensorFracIota IsFractionRing.map
  exact IsLocalization.map_eq
    (T := nonZeroDivisors ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ t

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem]
  [IsDomain ((toAffine E₀⁄F).FunctionField ⊗[F] F')]
  [IsDomain ((toAffine E₀'⁄F).FunctionField ⊗[F] F')] in
theorem kw_surge_hgf4_bcTensorIota_finite (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀).toRingHom.Finite :=
  RingHom.Finite.tensorProductMap (f := ι₀) hfin₀ (g := AlgHom.id F F') (RingHom.Finite.id F')

def kw_surge_hgf4_bcTensorFracIotaAlg :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →ₐ[F'] FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  { kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ with
    commutes' := fun c => by
      change kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ (algebraMap F' _ c)
          = algebraMap F' _ c
      rw [IsScalarTower.algebraMap_apply F' ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply,
        kw_surge_hgf4_bcTensorFracIota_algebraMap E₀ E₀' F F' ι₀,
        kw_surge_hgf4_bcTensorIota_tmul, map_one,
        IsScalarTower.algebraMap_apply F' ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply] }

def kw_surge_hgf4_bcIota₁ :
    (E₀'⁄F').toAffine.FunctionField →ₐ[F'] (E₀⁄F').toAffine.FunctionField :=
  let ψE := kw_functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneral E₀' F F'
  (ψE.symm.toAlgHom.comp (kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀)).comp
    ψE'.toAlgHom

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcTensorFracIotaSeam (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀).Finite ∧
    (letI := (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀).toAlgebra
     @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
       (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule)
      = finrankAlong F ι₀ := by
  classical
  let FF := (E₀⁄F).toAffine.FunctionField
  let FF' := (E₀'⁄F).toAffine.FunctionField
  let T := (E₀⁄F).toAffine.FunctionField ⊗[F] F'
  let T' := (E₀'⁄F).toAffine.FunctionField ⊗[F] F'
  let FrT := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
  let FrT' := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
  let ιT : T' →+* T := (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀).toRingHom
  let ιFr : FrT' →+* FrT := kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
  have hιT_inj : Function.Injective ιT :=
    kw_surge_hgf4_bcTensorIota_injective E₀ E₀' F F' ι₀
  have hιT_fin : ιT.Finite := kw_surge_hgf4_bcTensorIota_finite E₀ E₀' F F' ι₀ hfin₀
  have hιFr_am : ∀ t : T', ιFr (algebraMap T' FrT' t) = algebraMap T FrT (ιT t) :=
    kw_surge_hgf4_bcTensorFracIota_algebraMap E₀ E₀' F F' ι₀
  let algι : Algebra FF' FF := ι₀.toRingHom.toAlgebra
  let modι : Module FF' FF := Algebra.toModule
  have hsmul_ι : ∀ (c : FF') (x : FF), c • x = ι₀ c * x := fun c x => rfl
  have hfinFF : Module.Finite FF' FF := hfin₀
  have hfreeFF : Module.Free FF' FF := Module.Free.of_divisionRing FF' FF
  let D := finrankAlong F ι₀
  let b : Module.Basis (Fin D) FF' FF := Module.finBasisOfFinrankEq FF' FF (n := D) rfl
  have hrepr_mul : ∀ (c : FF') (x : FF) (j : Fin D),
      b.repr (ι₀ c * x) j = c * b.repr x j := fun c x j => by
    rw [← hsmul_ι, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e : Fin D → T := fun i => (b i) ⊗ₜ[F] (1 : F')
  let bFr : Fin D → FrT := fun i => algebraMap T FrT (e i)
  have hspanT : ∀ t : T, ∃ c : Fin D → T', t = ∑ i, ιT (c i) * e i := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨cx, hx⟩ := hx; obtain ⟨cy, hy⟩ := hy
      exact ⟨cx + cy, by simp only [Pi.add_apply, map_add, add_mul,
        Finset.sum_add_distrib, ← hx, ← hy]⟩
    | tmul a c =>
      refine ⟨fun i => (b.repr a i) ⊗ₜ[F] c, ?_⟩
      have hb_sum : a = ∑ i, ι₀ (b.repr a i) * b i := by
        conv_lhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
          Finsupp.sum_fintype _ _ (fun i => by rw [hsmul_ι, map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun i _ => hsmul_ι _ _
      calc (a ⊗ₜ[F] c : T)
          = (∑ i, ι₀ (b.repr a i) * b i) ⊗ₜ[F] c := by rw [← hb_sum]
        _ = ∑ i, ιT ((b.repr a i) ⊗ₜ[F] c) * e i := by
            rw [TensorProduct.sum_tmul]
            refine Finset.sum_congr rfl fun i _ => ?_
            show (ι₀ (b.repr a i) * b i) ⊗ₜ[F] c = ιT ((b.repr a i) ⊗ₜ[F] c) * e i
            rw [show ιT ((b.repr a i) ⊗ₜ[F] c) = (ι₀ (b.repr a i)) ⊗ₜ[F] c from
                  kw_surge_hgf4_bcTensorIota_tmul E₀ E₀' F F' ι₀ _ _,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hliT : ∀ c : Fin D → T', ∑ i, ιT (c i) * e i = 0 → ∀ j, c j = 0 := by
    intro c hc j
    let pj : FF →ₗ[F] FF' :=
      { toFun := fun x => b.repr x j
        map_add' := fun x y => by simp only [map_add, Finsupp.add_apply]
        map_smul' := fun f x => by
          simp only [RingHom.id_apply, Algebra.smul_def]
          have h := hrepr_mul (algebraMap F FF' f) x j
          rwa [ι₀.commutes] at h }
    let Ej : T →ₗ[F] T' := LinearMap.rTensor F' pj
    have hEj_key : ∀ (a : T') (i : Fin D),
        Ej (ιT a * e i) = if i = j then a else 0 := by
      intro a i
      induction a using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [map_add, add_mul, hx, hy]; split_ifs <;> simp
      | tmul x c' =>
        rw [show ιT ((x : FF') ⊗ₜ[F] c') = (ι₀ x) ⊗ₜ[F] c' from
              kw_surge_hgf4_bcTensorIota_tmul E₀ E₀' F F' ι₀ _ _,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        change (pj (ι₀ x * b i)) ⊗ₜ[F] c' = if i = j then (x : FF') ⊗ₜ[F] c' else 0
        rw [show pj (ι₀ x * b i) = if i = j then x else 0 from ?_]
        · split_ifs with h
          · rfl
          · exact TensorProduct.zero_tmul _ c'
        · change b.repr (ι₀ x * b i) j = if i = j then x else 0
          rw [hrepr_mul, b.repr_self, Finsupp.single_apply]
          split_ifs with h <;> simp
    have hc' : Ej (∑ i, ιT (c i) * e i) = 0 := by rw [hc, map_zero]
    simpa only [map_sum, hEj_key, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hc'
  obtain ⟨hspanFr, hliFr⟩ :=
    fractionRing_span_and_independent ιT ιFr hιT_inj hιT_fin hιFr_am e hspanT hliT
  let algFr : Algebra FrT' FrT := ιFr.toAlgebra
  let modFr : Module FrT' FrT := Algebra.toModule
  have hsmul_Fr : ∀ (c : FrT') (x : FrT), c • x = ιFr c * x := fun c x => rfl
  have hli_modFr : LinearIndependent FrT' bFr := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine hliFr g ?_ i
    simpa only [hsmul_Fr] using hg
  have hsp_modFr : ⊤ ≤ Submodule.span FrT' (Set.range bFr) := by
    intro z _
    obtain ⟨d, hd⟩ := hspanFr z
    rw [hd]
    exact Submodule.sum_mem _ fun i _ => (hsmul_Fr (d i) (bFr i)) ▸
      Submodule.smul_mem _ (d i) (Submodule.subset_span ⟨i, rfl⟩)
  let bFr' : Module.Basis (Fin D) FrT' FrT := .mk hli_modFr hsp_modFr
  refine ⟨Module.Finite.of_basis bFr', ?_⟩
  change Module.finrank FrT' FrT = D
  rw [Module.finrank_eq_card_basis bFr', Fintype.card_fin]

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [WeierstrassCurve.IsElliptic E₀⁄F]
  [(toAffine E₀⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)]
  [(toAffine E₀⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [(toAffine E₀'⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)]
  [(toAffine E₀'⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀⁄F']
  [(toAffine E₀⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')]
  [(toAffine E₀⁄F').AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F']
  [(toAffine E₀'⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')]
  [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcIota₁_finiteAlong (hfin₀ : FiniteAlong F ι₀) :
    FiniteAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀) := by
  have hFr_fin := (kw_surge_hgf4_bcTensorFracIotaSeam E₀ E₀' F F' ι₀ hfin₀).1
  let ψE := kw_functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneral E₀' F F'
  have h1 : RingHom.Finite ψE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE'.surjective
  have h2 : RingHom.Finite ψE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE.symm.surjective
  change RingHom.Finite (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom
  have hcomp : (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom
      = (ψE.symm.toAlgHom.toRingHom.comp
          (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀)).comp ψE'.toAlgHom.toRingHom := rfl
  rw [hcomp]
  exact RingHom.Finite.comp (RingHom.Finite.comp h2 hFr_fin) h1

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [WeierstrassCurve.IsElliptic E₀⁄F]
  [(toAffine E₀⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)]
  [(toAffine E₀⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [(toAffine E₀'⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)]
  [(toAffine E₀'⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀⁄F']
  [(toAffine E₀⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')]
  [(toAffine E₀⁄F').AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F']
  [(toAffine E₀'⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')]
  [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcIota₁_isIntegral (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom.IsIntegral :=
  RingHom.Finite.to_isIntegral
    (show RingHom.Finite (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom from
      kw_surge_hgf4_bcIota₁_finiteAlong E₀ E₀' F F' ι₀ hfin₀)

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [WeierstrassCurve.IsElliptic E₀⁄F]
  [(toAffine E₀⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)]
  [(toAffine E₀⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [(toAffine E₀'⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)]
  [(toAffine E₀'⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀⁄F']
  [(toAffine E₀⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')]
  [(toAffine E₀⁄F').AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F']
  [(toAffine E₀'⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')]
  [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcIota₁_finrankAlong (hfin₀ : FiniteAlong F ι₀) :
    finrankAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀) = finrankAlong F ι₀ := by
  let ψE := kw_functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneral E₀' F F'
  let ιFr := kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
  have hcomm : ∀ x, ιFr (ψE' x)
      = ψE (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀ x) := fun x => by
    change ιFr (ψE' x) = ψE (ψE.symm (_))
    exact (ψE.apply_symm_apply _).symm
  calc finrankAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀)
      = (letI := ιFr.toAlgebra
         @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
           (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule) :=
        @Algebra.finrank_eq_of_equiv_equiv
          (E₀'⁄F').toAffine.FunctionField (E₀⁄F').toAffine.FunctionField _ _
          (algebraAlong (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀))
          _ _ _ _ ιFr.toAlgebra ψE'.toRingEquiv ψE.toRingEquiv (RingHom.ext hcomm)
    _ = finrankAlong F ι₀ := (kw_surge_hgf4_bcTensorFracIotaSeam E₀ E₀' F F' ι₀ hfin₀).2

section Naturality

variable (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀)
variable (σ : F →ₐ[R₀] F') (hσ : ∀ c, σ c = algebraMap F F' c)

local notation "χE" => kw_functionFieldMapAlongGeneral E₀ F F'
local notation "χE'" => kw_functionFieldMapAlongGeneral E₀' F F'
local notation "ι₁" => kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀

theorem kw_surge_hgf4_place_inv_mem_of_isUnit {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : Place K L) {z : v.toValuationSubring} (hz : IsUnit z) :
    ((z : L))⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨w, hw⟩ := hz.exists_right_inv
  have hmul : (z : L) * (w : L) = 1 := by
    have h := congrArg (fun a : v.toValuationSubring => (a : L)) hw
    simpa using h
  rw [inv_eq_of_mul_eq_one_right hmul]; exact w.2

omit [DecidableEq F] [DecidableEq F'] in
omit [IsAlgClosed F] [CharZero F] [IsAlgClosed F'] [CharZero F'] in
theorem kw_surge_hgf4_toAffine_map_eq (V : WeierstrassCurve R₀) :
    (V⁄F).toAffine.map (algebraMap F F') = (V⁄F').toAffine := by
  classical
  change ((V.map (algebraMap R₀ F)).map (algebraMap F F')).toAffine = (V.map (algebraMap R₀
    F')).toAffine
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R₀ F F']

open CoordinateRing in
omit [IsAlgClosed F] [CharZero F] [IsAlgClosed F'] [CharZero F'] in
theorem kw_surge_hgf4_χE_algebraMap_XClass (V : WeierstrassCurve R₀) [V.IsElliptic]
    [(V⁄F).IsElliptic] [(V⁄F).toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (V⁄F).toAffine]
    [(V⁄F).toAffine.AbelTheorem] [(V⁄F').IsElliptic]
    [(V⁄F').toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (V⁄F').toAffine]
    [(V⁄F').toAffine.AbelTheorem] (x : F) :
    kw_functionFieldMapAlongGeneral V F F'
        (algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
          (XClass (V⁄F).toAffine x))
      = algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
          (XClass (V⁄F').toAffine (algebraMap F F' x)) := by
  have hF : algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
      (XClass (V⁄F).toAffine x)
      = polyToFunctionField (V⁄F).toAffine X - algebraMap F (V⁄F).toAffine.FunctionField x := by
    rw [← polyToFunctionField_C, ← map_sub]; rfl
  have hF' : algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
      (XClass (V⁄F').toAffine (algebraMap F F' x))
      = polyToFunctionField (V⁄F').toAffine X
          - algebraMap F' (V⁄F').toAffine.FunctionField (algebraMap F F' x) := by
    rw [← polyToFunctionField_C, ← map_sub]; rfl
  rw [hF, hF', map_sub, kw_functionFieldMapAlongGeneral_polyToFunctionField_X,
    AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (V⁄F').toAffine.FunctionField]

open CoordinateRing in
omit [IsAlgClosed F] [CharZero F] [IsAlgClosed F'] [CharZero F'] in
theorem kw_surge_hgf4_χE_algebraMap_YClass (V : WeierstrassCurve R₀) [V.IsElliptic]
    [(V⁄F).IsElliptic] [(V⁄F).toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (V⁄F).toAffine] [(V⁄F).toAffine.AbelTheorem] [(V⁄F').IsElliptic]
    [(V⁄F').toAffine.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (V⁄F').toAffine]
    [(V⁄F').toAffine.AbelTheorem] (y : F) :
    kw_functionFieldMapAlongGeneral V F F'
        (algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
          (YClass (V⁄F).toAffine (C y)))
      = algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
          (YClass (V⁄F').toAffine (C (algebraMap F F' y))) := by
  have hF : algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
      (YClass (V⁄F).toAffine (C y))
      = yGen (V⁄F).toAffine - algebraMap F (V⁄F).toAffine.FunctionField y := by
    rw [YClass, map_sub, map_sub, yGen]
    congr 1
  have hF' : algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
      (YClass (V⁄F').toAffine (C (algebraMap F F' y)))
      = yGen (V⁄F').toAffine
          - algebraMap F' (V⁄F').toAffine.FunctionField (algebraMap F F' y) := by
    rw [YClass, map_sub, map_sub, yGen]
    congr 1
  rw [hF, hF', map_sub, kw_functionFieldMapAlongGeneral_yGen,
    AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (V⁄F').toAffine.FunctionField]

omit [IsDomain ((toAffine E₀⁄F).FunctionField ⊗[F] F')] in
omit [CharZero F] [CharZero F'] in
theorem kw_surge_hgf4_χE_VSR_compat {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y)
    (hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y))
    (g : (E₀⁄F).toAffine.FunctionField) :
    χE g ∈ (placeOfEquation hσP.left).toValuationSubring ↔
      g ∈ (placeOfEquation hP.left).toValuationSubring := by
  have hχE_inj : Function.Injective (χE : _ →ₐ[F] _) :=
    (kw_functionFieldMapAlongGeneral E₀ F F').injective
  classical
  have hmk (W : Affine F) : ∀ q : F[X][Y],
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W q)
        = q.eval₂ (polyToFunctionField W) (yGen W) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p r hp hr => rw [map_add, map_add, Polynomial.eval₂_add, hp, hr]
    | monomial n a =>
        simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
          Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rw [← algebraMap_polynomial_eq_mk_C, ← polyToFunctionField_apply]; rfl
  have hfinσP : IsFinitePlace (placeOfEquation hσP.left) :=
    isFinitePlace_placeOfEquation hσP.left
  have hχE_polyToFF (p : F[X]) :
      χE (polyToFunctionField (E₀⁄F).toAffine p) ∈ (placeOfEquation hσP.left).toValuationSubring
        := by
    have h : χE (polyToFunctionField (E₀⁄F).toAffine p)
        = polyToFunctionField (E₀⁄F').toAffine (p.map (algebraMap F F')) := by
      induction p using Polynomial.induction_on' with
      | add r s hr hs => rw [map_add, map_add, Polynomial.map_add, map_add, hr, hs]
      | monomial n c =>
          rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
            ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow,
            map_mul, map_pow, polyToFunctionField_C, polyToFunctionField_C,
            kw_functionFieldMapAlongGeneral_polyToFunctionField_X, AlgHom.commutes,
            IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]
    rw [h, polyToFunctionField_apply]
    exact hfinσP _
  have hχE_CR_mem : ∀ a : (E₀⁄F).toAffine.CoordinateRing,
      χE (algebraMap _ _ a) ∈ (placeOfEquation hσP.left).toValuationSubring := by
    intro a
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hmk (E₀⁄F).toAffine q]
    induction q using Polynomial.induction_on' with
    | add r s hr hs =>
        rw [Polynomial.eval₂_add, map_add]
        exact Subring.add_mem _ hr hs
    | monomial n p =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
          Polynomial.eval₂_C, Polynomial.eval₂_X, map_mul, map_pow,
          kw_functionFieldMapAlongGeneral_yGen]
        exact Subring.mul_mem _ (hχE_polyToFF p)
          (Subring.pow_mem _ (hfinσP (CoordinateRing.mk (E₀⁄F').toAffine Y)) n)
  have hXClass_σP_mem_𝔪 : (⟨algebraMap _ _ (CoordinateRing.XClass (E₀⁄F').toAffine
        (algebraMap F F' x)), hfinσP _⟩ : (placeOfEquation hσP.left).toValuationSubring)
      ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_ord_pos _
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (CoordinateRing.XClass_ne_zero _))]
    exact (ord_placeOfEquation_pos_iff hσP.left (CoordinateRing.XClass_ne_zero _)).mpr
      (Ideal.subset_span (Set.mem_insert _ _))
  have hYClass_σP_mem_𝔪 : (⟨algebraMap _ _ (CoordinateRing.YClass (E₀⁄F').toAffine
        (C (algebraMap F F' y))), hfinσP _⟩ : (placeOfEquation hσP.left).toValuationSubring)
      ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_ord_pos _
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (CoordinateRing.YClass_ne_zero _))]
    exact (ord_placeOfEquation_pos_iff hσP.left (CoordinateRing.YClass_ne_zero _)).mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hχE_mem_𝔪 : ∀ a ∈ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y),
      (⟨χE (algebraMap _ _ a), hχE_CR_mem a⟩ : (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    intro a ha
    rw [CoordinateRing.XYIdeal, Ideal.mem_span_pair] at ha
    obtain ⟨p, q, hpq⟩ := ha
    have hdecomp : χE (algebraMap _ _ a)
        = χE (algebraMap _ _ p) * χE (algebraMap _ _ (CoordinateRing.XClass (E₀⁄F).toAffine x))
          + χE (algebraMap _ _ q)
            * χE (algebraMap _ _ (CoordinateRing.YClass (E₀⁄F).toAffine (C y))) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, hpq]
    rw [show (⟨χE (algebraMap _ _ a), hχE_CR_mem a⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        = ⟨χE (algebraMap _ _ p), hχE_CR_mem p⟩
            * ⟨_, hfinσP (CoordinateRing.XClass (E₀⁄F').toAffine (algebraMap F F' x))⟩
          + ⟨χE (algebraMap _ _ q), hχE_CR_mem q⟩
            * ⟨_, hfinσP (CoordinateRing.YClass (E₀⁄F').toAffine (C (algebraMap F F' y)))⟩ from
        Subtype.ext (by
          push_cast
          rw [hdecomp, kw_surge_hgf4_χE_algebraMap_XClass F F' E₀ x,
            kw_surge_hgf4_χE_algebraMap_YClass F F' E₀ y])]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hXClass_σP_mem_𝔪)
      (Ideal.mul_mem_left _ _ hYClass_σP_mem_𝔪)
  have hχE_unit : ∀ s : (E₀⁄F).toAffine.CoordinateRing,
      s ∉ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y) →
      IsUnit (⟨χE (algebraMap _ _ s), hχE_CR_mem s⟩ :
        (placeOfEquation hσP.left).toValuationSubring) := by
    intro s hs
    obtain ⟨c, hc⟩ := CoordinateRing.exists_sub_algebraMap_mem hP.left s
    have hc_ne : c ≠ 0 := by
      intro h; apply hs; simpa [h, sub_zero] using hc
    have hσc_ne : algebraMap F F' c ≠ 0 := (map_ne_zero_iff _ (algebraMap F F').injective).mpr hc_ne
    have hχE_const : χE (algebraMap (E₀⁄F).toAffine.CoordinateRing _
          (algebraMap F (E₀⁄F).toAffine.CoordinateRing c))
        = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c) := by
      rw [← IsScalarTower.algebraMap_apply F (E₀⁄F).toAffine.CoordinateRing
        (E₀⁄F).toAffine.FunctionField, AlgHom.commutes,
        IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]
    have hsplit : (⟨χE (algebraMap _ _ s), hχE_CR_mem s⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        = ⟨algebraMap F' _ (algebraMap F F' c),
            (placeOfEquation hσP.left).algebraMap_mem' _⟩
          + ⟨χE (algebraMap _ _ (s - algebraMap F _ c)), hχE_CR_mem _⟩ := by
      refine Subtype.ext ?_
      change χE (algebraMap _ _ s)
          = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c)
            + χE (algebraMap _ _ (s - algebraMap F _ c))
      rw [← hχE_const, ← map_add, ← map_add, add_sub_cancel]
    rw [hsplit]
    have hfirst_unit : IsUnit (⟨algebraMap F' _ (algebraMap F F' c),
        (placeOfEquation hσP.left).algebraMap_mem' _⟩ :
        (placeOfEquation hσP.left).toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap F' _ (algebraMap F F' c)⁻¹,
        (placeOfEquation hσP.left).algebraMap_mem' _⟩, Subtype.ext ?_⟩
      push_cast
      rw [← map_inv₀, ← map_mul, mul_inv_cancel₀ hσc_ne, map_one]
    have hsecond_𝔪 := hχE_mem_𝔪 (s - algebraMap F _ c) hc
    by_contra hnotunit
    have hsum_𝔪 := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnotunit)
    have hfirst_𝔪 : (⟨algebraMap F' _ (algebraMap F F' c),
          (placeOfEquation hσP.left).algebraMap_mem' _⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal _ := by
      have hsub := Ideal.sub_mem _ hsum_𝔪 hsecond_𝔪
      rwa [add_sub_cancel_right] at hsub
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hfirst_𝔪)) hfirst_unit
  have hmem_P := mem_placeOfEquation_iff_fraction (E₀⁄F).toAffine hP
  constructor
  · intro hχEg
    by_contra hg_notin
    have hg_ne : g ≠ 0 := fun h => hg_notin (h ▸ Subring.zero_mem _)
    have hginv_in : g⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
      ((placeOfEquation hP.left).toValuationSubring.mem_or_inv_mem g).resolve_left hg_notin
    obtain ⟨n, s, hs_notin, hginv_eq⟩ := (hmem_P g⁻¹).mp hginv_in
    have hginv_𝔪 : (⟨g⁻¹, hginv_in⟩ : (placeOfEquation hP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal _ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hg_notin (inv_inv g ▸ kw_surge_hgf4_place_inv_mem_of_isUnit _ hu)
    have hn_in : n ∈ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y) := by
      by_contra hn_notin
      have hfinP := isFinitePlace_placeOfEquation hP.left
      have hn_inv : (algebraMap _ _ n)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
        hfinP.inv_mem (by rwa [centre_placeOfEquation])
      have hs_inv : (algebraMap _ _ s)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
        hfinP.inv_mem (by rwa [centre_placeOfEquation])
      have hginv_unit : IsUnit
          (⟨g⁻¹, hginv_in⟩ : (placeOfEquation hP.left).toValuationSubring) := by
        have hg_mem : g ∈ (placeOfEquation hP.left).toValuationSubring := by
          have : g = algebraMap _ _ s * (algebraMap _ _ n)⁻¹ := by
            rw [← inv_inv g, hginv_eq, mul_inv, inv_inv, mul_comm]
          rw [this]; exact Subring.mul_mem _ (hfinP s) hn_inv
        exact isUnit_iff_exists_inv.mpr
          ⟨(⟨g, hg_mem⟩ : (placeOfEquation hP.left).toValuationSubring),
           Subtype.ext (by push_cast; exact inv_mul_cancel₀ hg_ne)⟩
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hginv_𝔪) hginv_unit
    have hχEn_𝔪 := hχE_mem_𝔪 n hn_in
    have hχEs_unit := hχE_unit s hs_notin
    have hχEginv_eq : χE g⁻¹ = χE (algebraMap _ _ n) * (χE (algebraMap _ _ s))⁻¹ := by
      rw [hginv_eq, map_mul, map_inv₀]
    have hχEginv_mem : χE g⁻¹ ∈ (placeOfEquation hσP.left).toValuationSubring := by
      rw [hχEginv_eq]
      exact Subring.mul_mem _ (hχE_CR_mem n)
        (kw_surge_hgf4_place_inv_mem_of_isUnit _ hχEs_unit)
    have hχEginv_𝔪 : (⟨χE g⁻¹, hχEginv_mem⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
      have hχEs_inv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hχEs_unit
      have hrw : (⟨χE g⁻¹, hχEginv_mem⟩ : (placeOfEquation hσP.left).toValuationSubring)
          = (⟨χE (algebraMap _ _ n), hχE_CR_mem n⟩ :
              (placeOfEquation hσP.left).toValuationSubring)
            * ⟨(χE (algebraMap _ _ s))⁻¹, hχEs_inv_mem⟩ :=
        Subtype.ext (by change χE g⁻¹ = _ * _; exact hχEginv_eq)
      rw [hrw]
      exact Ideal.mul_mem_right _ _ hχEn_𝔪
    have hχEg_ne : χE g ≠ 0 := (map_ne_zero_iff _ hχE_inj).mpr hg_ne
    have hχEginv_unit : IsUnit
        (⟨χE g⁻¹, hχEginv_mem⟩ : (placeOfEquation hσP.left).toValuationSubring) :=
      isUnit_iff_exists_inv.mpr
        ⟨(⟨χE g, hχEg⟩ : (placeOfEquation hσP.left).toValuationSubring),
         Subtype.ext (by change χE g⁻¹ * χE g = 1; rw [map_inv₀, inv_mul_cancel₀ hχEg_ne])⟩
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hχEginv_𝔪) hχEginv_unit
  · intro hg
    obtain ⟨n, s, hs_notin, hg_eq⟩ := (hmem_P g).mp hg
    rw [hg_eq, map_mul, map_inv₀]
    exact Subring.mul_mem _ (hχE_CR_mem n)
      (kw_surge_hgf4_place_inv_mem_of_isUnit _ (hχE_unit s hs_notin))

omit [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [(toAffine E₀'⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)]
  [(toAffine E₀'⁄F).AbelTheorem] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [(toAffine E₀'⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')]
  [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcIota₁_compat (a : (E₀'⁄F).toAffine.FunctionField) :
    (ι₁) (χE' a) = χE (ι₀ a) := by
  let ψE := kw_functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneral E₀' F F'
  have hκE' : ψE' (χE' a)
      = algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')) := by
    have hκ : ((kw_functionFieldTensorFracHomGeneral E₀' F F').restrictScalars F).comp
        (kw_functionFieldMapAlongGeneral E₀' F F')
        = (IsScalarTower.toAlgHom F ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine kw_functionField_algHom_ext ?_ ?_
      · change kw_functionFieldTensorFracHomGeneral E₀' F F' (χE' _) = _
        rw [kw_functionFieldMapAlongGeneral_polyToFunctionField_X,
          kw_functionFieldTensorFracHomGeneral_X]; rfl
      · change kw_functionFieldTensorFracHomGeneral E₀' F F' (χE' _) = _
        rw [kw_functionFieldMapAlongGeneral_yGen, kw_functionFieldTensorFracHomGeneral_yGen]
        rfl
    exact DFunLike.congr_fun hκ a
  have hκE : ∀ b, ψE.symm (algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
      (b ⊗ₜ[F] (1 : F'))) = χE b := by
    intro b
    refine ψE.injective ?_
    rw [AlgEquiv.apply_symm_apply]
    have hκ : ((kw_functionFieldTensorFracHomGeneral E₀ F F').restrictScalars F).comp
        (kw_functionFieldMapAlongGeneral E₀ F F')
        = (IsScalarTower.toAlgHom F ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine kw_functionField_algHom_ext ?_ ?_
      · change kw_functionFieldTensorFracHomGeneral E₀ F F' (χE _) = _
        rw [kw_functionFieldMapAlongGeneral_polyToFunctionField_X,
          kw_functionFieldTensorFracHomGeneral_X]; rfl
      · change kw_functionFieldTensorFracHomGeneral E₀ F F' (χE _) = _
        rw [kw_functionFieldMapAlongGeneral_yGen, kw_functionFieldTensorFracHomGeneral_yGen]
        rfl
    exact (DFunLike.congr_fun hκ b).symm
  change ψE.symm (kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀ (ψE' (χE' a)))
      = χE (ι₀ a)
  rw [hκE',
    show kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')))
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _ ((ι₀ a) ⊗ₜ[F] (1 : F')) from by
        change kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ _ = _
        rw [kw_surge_hgf4_bcTensorFracIota_algebraMap, kw_surge_hgf4_bcTensorIota_tmul],
    hκE (ι₀ a)]

omit [IsDomain ((toAffine E₀⁄F).FunctionField ⊗[F] F')] in
omit [CharZero F] [CharZero F'] in
/-- Positivity of the order at an affine point is preserved by scalar extension. -/
theorem baseChange_ord_pos_iff {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y)
    (hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y))
    (h : (E₀⁄F).toAffine.FunctionField) (hh : h ≠ 0) :
    0 < (placeOfEquation hσP.left).ord (χE h) ↔
      0 < (placeOfEquation hP.left).ord h := by
  have hχEh_ne : χE h ≠ 0 :=
    (map_ne_zero_iff _ (kw_functionFieldMapAlongGeneral E₀ F F').injective).mpr hh
  have hVSR := kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP
  constructor <;> intro hpos
  · have hχEh_mem : χE h ∈ (placeOfEquation hσP.left).toValuationSubring :=
      AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfEquation hσP.left) hχEh_ne hpos.le
    have hh_mem : h ∈ (placeOfEquation hP.left).toValuationSubring := (hVSR h).mp hχEh_mem
    rw [← Place.mem_maximalIdeal_iff_ord_pos _ hh hh_mem,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hinv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hu
    have hχEinv_mem : χE h⁻¹ ∈ (placeOfEquation hσP.left).toValuationSubring :=
      (hVSR h⁻¹).mpr hinv_mem
    rw [map_inv₀] at hχEinv_mem
    have hχEh_unit : IsUnit
        (⟨χE h, hχEh_mem⟩ : (placeOfEquation hσP.left).toValuationSubring) :=
      isUnit_iff_exists_inv.mpr ⟨⟨(χE h)⁻¹, hχEinv_mem⟩,
        Subtype.ext (mul_inv_cancel₀ hχEh_ne)⟩
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
      ((Place.mem_maximalIdeal_iff_ord_pos _ hχEh_ne hχEh_mem).mpr hpos))) hχEh_unit
  · have hh_mem : h ∈ (placeOfEquation hP.left).toValuationSubring :=
      AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfEquation hP.left) hh hpos.le
    have hχEh_mem : χE h ∈ (placeOfEquation hσP.left).toValuationSubring :=
      (hVSR h).mpr hh_mem
    rw [← Place.mem_maximalIdeal_iff_ord_pos _ hχEh_ne hχEh_mem,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hinv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hu
    have hh_inv_mem : h⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring := by
      rw [← map_inv₀] at hinv_mem; exact (hVSR h⁻¹).mp hinv_mem
    have hh_unit : IsUnit
        (⟨h, hh_mem⟩ : (placeOfEquation hP.left).toValuationSubring) :=
      isUnit_iff_exists_inv.mpr ⟨⟨h⁻¹, hh_inv_mem⟩, Subtype.ext (mul_inv_cancel₀ hh)⟩
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
      ((Place.mem_maximalIdeal_iff_ord_pos _ hh hh_mem).mpr hpos))) hh_unit

include hσ in
omit [E₀'.IsElliptic] in
theorem kw_surge_hgf4_pmop_naturality :
    let hι₁ := kw_surge_hgf4_bcIota₁_isIntegral E₀ E₀' F F' ι₀ hfin₀
    let hfin₁ := kw_surge_hgf4_bcIota₁_finiteAlong E₀ E₀' F F' ι₀ hfin₀
    let σE : (E₀⁄F).toAffine.Point →+ (E₀⁄F').toAffine.Point := Point.map (W' := E₀.toAffine) σ
    let σE' : (E₀'⁄F).toAffine.Point →+ (E₀'⁄F').toAffine.Point := Point.map (W' := E₀'.toAffine) σ
    let φ₀ := pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀)
    let φ₁ := pointMapOfPushforward (ι₁) hι₁ hfin₁ (normFormulaAlong_of_elliptic (ι₁) hfin₁)
    ∀ P, φ₁ (σE P) = σE' (φ₀ P) := by
  intro hι₁ hfin₁ σE σE' φ₀ φ₁
  have hgBC₀ := kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι₀ hι₀ hfin₀
    (normFormulaAlong_of_elliptic ι₀ hfin₀)
  have hgBC₁ := kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub (ι₁) hι₁ hfin₁
    (normFormulaAlong_of_elliptic ι₁ hfin₁)
  let g₀ := kw_fdn2_qephod_hend7_geomMorphBC ι₀ hι₀
  let g₁ := kw_fdn2_qephod_hend7_geomMorphBC (ι₁) hι₁
  have hgBC_nat_affine : ∀ {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y),
      g₁ (σE (.some x y hP)) = σE' (g₀ (.some x y hP)) := by
    intro x y hP
    have hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y) :=
      kw_surge_hgf4_toAffine_map_eq F F' E₀ ▸
        (((E₀⁄F).toAffine.map_nonsingular (algebraMap F F').injective x y).mpr hP)
    have hσE_some : σE (.some x y hP) = .some _ _ hσP := by grind [Point.map_some]
    refine placeOfPoint_injective ?_
    rw [← kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι₁ hι₁ (σE (.some x y hP)),
      hσE_some, placeOfPoint_some]
    have hseam₀ : (placeOfEquation hP.left).restrictAlong ι₀ hι₀
        = placeOfPoint (g₀ (.some x y hP)) := by
      rw [← placeOfPoint_some hP,
        kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι₀ hι₀]
    have hι₁X : (ι₁) (polyToFunctionField (E₀'⁄F').toAffine X)
        = χE (ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)) := by
      rw [← kw_functionFieldMapAlongGeneral_polyToFunctionField_X E₀' F F']
      exact kw_surge_hgf4_bcIota₁_compat E₀ E₀' F F' ι₀ _
    have hι₁Y : (ι₁) (yGen (E₀'⁄F').toAffine)
        = χE (ι₀ (yGen (E₀'⁄F).toAffine)) := by
      rw [← kw_functionFieldMapAlongGeneral_yGen E₀' F F']
      exact kw_surge_hgf4_bcIota₁_compat E₀ E₀' F F' ι₀ _
    have hχE_const : ∀ c : F, χE (algebraMap F (E₀⁄F).toAffine.FunctionField c)
        = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c) := fun c => by
      rw [AlgHom.commutes,
        IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]
    rcases hQ₀_case : g₀ (.some x y hP) with _ | ⟨qx, qy, hQ₀ns⟩
    · rw [show placeOfPoint (σE' (.zero : (E₀'⁄F).toAffine.Point))
          = (InfinitePlace.place : Place F' (E₀'⁄F').toAffine.FunctionField) from by
        rw [show σE' (.zero : (E₀'⁄F).toAffine.Point)
            = (.zero : (E₀'⁄F').toAffine.Point) from map_zero σE', placeOfPoint_zero]]
      refine AbstractSeam.restrictAlong_eq_infinitePlace (ι₁) hι₁ rfl _ ?_
      rw [hι₁X]
      intro hmem
      have hι₀X_mem : ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)
          ∈ (placeOfEquation hP.left).toValuationSubring :=
        (kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP _).mp hmem
      have hX_res : polyToFunctionField (E₀'⁄F).toAffine X
          ∈ ((placeOfEquation hP.left).restrictAlong ι₀ hι₀).toValuationSubring :=
        (Place.mem_restrictAlong_iff ι₀ hι₀ _ _).mpr hι₀X_mem
      rw [hseam₀, hQ₀_case, placeOfPoint_zero] at hX_res
      exact InfinitePlace.not_isFinitePlace (isFinitePlace_of_mem _ hX_res)
    · have hσQ : (E₀'⁄F').toAffine.Nonsingular (algebraMap F F' qx) (algebraMap F F' qy) :=
        kw_surge_hgf4_toAffine_map_eq F F' E₀' ▸
          (((E₀'⁄F).toAffine.map_nonsingular (algebraMap F F').injective qx qy).mpr hQ₀ns)
      have hσE'_some : σE' (.some qx qy hQ₀ns)
          = .some (algebraMap F F' qx) (algebraMap F F' qy) hσQ := by
        have h := Point.map_some (W' := E₀'.toAffine) (F := F) (K := F') σ hQ₀ns
        grind
      rw [hσE'_some, placeOfPoint_some]
      have hseam₀' : (placeOfEquation hP.left).restrictAlong ι₀ hι₀
          = placeOfEquation hQ₀ns.left := by rw [hseam₀, hQ₀_case, placeOfPoint_some]
      have hbrX : algebraMap (E₀'⁄F).toAffine.CoordinateRing (E₀'⁄F).toAffine.FunctionField
          (CoordinateRing.XClass (E₀'⁄F).toAffine qx)
          = polyToFunctionField (E₀'⁄F).toAffine X - algebraMap F _ qx :=
        AbstractSeam.map_XClass (V := (E₀'⁄F).toAffine) (W := (E₀'⁄F).toAffine)
          (AlgHom.id F (E₀'⁄F).toAffine.FunctionField) rfl qx
      have hbrY : algebraMap (E₀'⁄F).toAffine.CoordinateRing (E₀'⁄F).toAffine.FunctionField
          (CoordinateRing.YClass (E₀'⁄F).toAffine (C qy))
          = yGen (E₀'⁄F).toAffine - algebraMap F _ qy :=
        AbstractSeam.map_YClass (V := (E₀'⁄F).toAffine) (W := (E₀'⁄F).toAffine)
          (AlgHom.id F (E₀'⁄F).toAffine.FunctionField) rfl qy
      have hι₀X_ne : ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)
          - algebraMap F _ qx ≠ 0 := by
        rw [← ι₀.commutes, ← map_sub, ← hbrX]
        exact fun h => (CoordinateRing.XClass_ne_zero qx)
          ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp (ι₀.injective
            (h.trans (map_zero ι₀).symm)))
      have hι₀Y_ne : ι₀ (yGen (E₀'⁄F).toAffine) - algebraMap F _ qy ≠ 0 := by
        rw [← ι₀.commutes, ← map_sub, ← hbrY]
        exact fun h => (CoordinateRing.YClass_ne_zero (C qy))
          ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp (ι₀.injective
            (h.trans (map_zero ι₀).symm)))
      have hram_pos : 0 < Place.ramificationIndexAlong ι₀ (placeOfEquation hP.left) :=
        Place.ramificationIndexAlong_pos ι₀ hι₀ (placeOfEquation hP.left)
      have hdxF : 0 < (placeOfEquation hP.left).ord
          (ι₀ (polyToFunctionField (E₀'⁄F).toAffine X) - algebraMap F _ qx) := by
        rw [← ι₀.commutes, ← map_sub, ← hbrX,
          Place.ord_restrictAlong ι₀ hι₀, hseam₀']
        have hQord : 0 < (placeOfEquation hQ₀ns.left).ord (algebraMap _ _
            (CoordinateRing.XClass (E₀'⁄F).toAffine qx)) :=
          (ord_placeOfEquation_pos_iff hQ₀ns.left (CoordinateRing.XClass_ne_zero _)).mpr
            (Ideal.subset_span (Set.mem_insert _ _))
        positivity
      have hdyF : 0 < (placeOfEquation hP.left).ord
          (ι₀ (yGen (E₀'⁄F).toAffine) - algebraMap F _ qy) := by
        rw [← ι₀.commutes, ← map_sub, ← hbrY,
          Place.ord_restrictAlong ι₀ hι₀, hseam₀']
        have hQord : 0 < (placeOfEquation hQ₀ns.left).ord (algebraMap _ _
            (CoordinateRing.YClass (E₀'⁄F).toAffine (C qy))) :=
          (ord_placeOfEquation_pos_iff hQ₀ns.left (CoordinateRing.YClass_ne_zero _)).mpr
            (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
        positivity
      refine AbstractSeam.restrictAlong_placeOfEquation (ι₁) hι₁ rfl rfl
        hσP.left hσQ.left ?_ ?_ ?_
      · rw [hι₁X]
        refine (kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP _).mpr ?_
        rw [← Place.mem_restrictAlong_iff ι₀ hι₀, hseam₀']
        exact isFinitePlace_placeOfEquation hQ₀ns.left _
      · rw [hι₁X, ← hχE_const qx, ← map_sub]
        exact (baseChange_ord_pos_iff E₀ F F' hP hσP _ hι₀X_ne).mpr hdxF
      · rw [hι₁Y, ← hχE_const qy, ← map_sub]
        exact (baseChange_ord_pos_iff E₀ F F' hP hσP _ hι₀Y_ne).mpr hdyF
  let δ : (E₀⁄F).toAffine.Point →+ (E₀'⁄F').toAffine.Point :=
    (φ₁.comp σE) - (σE'.comp φ₀)
  have hδ_affine : ∀ {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y),
      δ (.some x y hP) = σE' (g₀ 0) - g₁ 0 := by
    intro x y hP
    change φ₁ (σE (.some x y hP)) - σE' (φ₀ (.some x y hP)) = _
    grind [hgBC_nat_affine hP]
  have hC_zero : σE' (g₀ 0) - g₁ 0 = 0 := by
    obtain ⟨e3⟩ := nonempty_pointTorsionBy_zmod (W := (E₀⁄F)) (n := 3) (by omega)
    let P₀ : (E₀⁄F).toAffine.Point := (e3.symm (fun _ => 1) : _)
    have hP₀_3 : (3 : ℤ) • P₀ = 0 := by
      have := (e3.symm (fun _ => 1)).2
      simp [P₀]
    have hP₀_ne : P₀ ≠ 0 := by
      intro h
      have heq : e3.symm (fun _ => 1) = 0 :=
        Subtype.ext (show (e3.symm (fun _ => 1) : (E₀⁄F).toAffine.Point) = 0 from h)
      have hfun : (fun _ => (1 : ZMod 3)) = (0 : Fin 2 → ZMod 3) := by
        have := congrArg e3 heq
        rwa [e3.apply_symm_apply, map_zero] at this
      exact one_ne_zero (congrFun hfun 0)
    have h2P₀_ne : (2 : ℤ) • P₀ ≠ 0 := by
      refine fun h2 ↦ hP₀_ne ?_
      have : (3 : ℤ) • P₀ - (2 : ℤ) • P₀ = 0 := by rw [hP₀_3, h2, sub_zero]
      simpa [← sub_smul]
    rcases hP₀_case : P₀ with _ | ⟨px, py, hpP⟩
    · exact (hP₀_ne hP₀_case).elim
    rcases h2P₀_case : (2 : ℤ) • P₀ with _ | ⟨qx, qy, hqQ⟩
    · exact (h2P₀_ne h2P₀_case).elim
    · grind
  intro P
  have hδP : δ P = 0 := by
    rcases P with _ | ⟨x, y, hP⟩
    · exact map_zero δ
    · rw [hδ_affine hP, hC_zero]
  exact sub_eq_zero.mp hδP

end Naturality
end BetweenCurvesTensor

end ModularCurve

namespace WeierstrassCurve.Affine

universe u

public section

variable {R₀ : Type u} [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']
variable [(E₀⁄F).IsElliptic] [(E₀⁄F).toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (E₀⁄F).toAffine] [(E₀⁄F).toAffine.AbelTheorem]
    [(E₀'⁄F).IsElliptic] [(E₀'⁄F).toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (E₀'⁄F).toAffine] [(E₀'⁄F).toAffine.AbelTheorem]
    [(E₀⁄F').IsElliptic] [(E₀⁄F').toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (E₀⁄F').toAffine] [(E₀⁄F').toAffine.AbelTheorem]
    [(E₀'⁄F').IsElliptic] [(E₀'⁄F').toAffine.GenusOnePlaceGate]
    [GenusOnePlaceGate.IsCentred (E₀'⁄F').toAffine] [(E₀'⁄F').toAffine.AbelTheorem]
variable (ι₀ : (E₀'⁄F).toAffine.FunctionField →ₐ[F] (E₀⁄F).toAffine.FunctionField)

/-- A finite function-field map base changes with the same degree, compatibly with scalar
extension on function fields and with the induced homomorphisms on elliptic-curve points. -/
theorem exists_functionFieldHom_baseChange_compatible
    (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀) :
    ∃ (ι₁ : (E₀'⁄F').toAffine.FunctionField →ₐ[F'] (E₀⁄F').toAffine.FunctionField)
      (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F' ι₁),
      finrankAlong F' ι₁ = finrankAlong F ι₀ ∧
      (∀ a, ι₁ (kw_functionFieldMapAlongGeneral E₀' F F' a) =
        kw_functionFieldMapAlongGeneral E₀ F F' (ι₀ a)) ∧
      (∀ P, pointMapOfPushforward ι₁ hι₁ hfin₁
          (normFormulaAlong_of_elliptic ι₁ hfin₁)
          (Point.map (W' := E₀.toAffine) (IsScalarTower.toAlgHom R₀ F F') P) =
        Point.map (W' := E₀'.toAffine) (IsScalarTower.toAlgHom R₀ F F')
          (pointMapOfPushforward ι₀ hι₀ hfin₀
            (normFormulaAlong_of_elliptic ι₀ hfin₀) P)) := by
  have : IsDomain ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
    kw_functionFieldTensorIsDomain_dischargeGeneral E₀ F F'
  have : IsDomain ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') :=
    kw_functionFieldTensorIsDomain_dischargeGeneral E₀' F F'
  refine ⟨kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀,
    kw_surge_hgf4_bcIota₁_isIntegral E₀ E₀' F F' ι₀ hfin₀,
    kw_surge_hgf4_bcIota₁_finiteAlong E₀ E₀' F F' ι₀ hfin₀,
    kw_surge_hgf4_bcIota₁_finrankAlong E₀ E₀' F F' ι₀ hfin₀,
    kw_surge_hgf4_bcIota₁_compat E₀ E₀' F F' ι₀, ?_⟩
  exact kw_surge_hgf4_pmop_naturality E₀ E₀' F F' ι₀ hι₀ hfin₀
    (IsScalarTower.toAlgHom R₀ F F') (fun _ => rfl)

end
end Affine
end WeierstrassCurve
