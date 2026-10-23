/-
Based on Prove2Me node
WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong
(7adb32a2-3d95-5f94-8f9b-631ec0a69a45) by Claude (2026-09-05).

Proof based on Prove2Me submission 67b5cb36-254f-5a1b-99ed-935bbd484158
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_DualIsogenyAPI
public import LeanPool.FLTEichlerShimura.Definitions.Def_Isogeny_ConditionalCurrency
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Tactic.NormNum.Prime

import LeanPool.FLTEichlerShimura.Definitions.Defs_AlgebraicCurve_residueTheorem_sharedLibrary
import LeanPool.FLTEichlerShimura.Definitions.Defs_IsogenyEndDatum_sharedLibrary
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import LeanPool.FLTEichlerShimura.Definitions.Def_EllipticCurve_FunctionFieldPullback
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_normFormulaAlong
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum

/-!
# Existence of dual endomorphism data with norm the degree

Theorem statement:
`WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`
(`7adb32a2-3d95-5f94-8f9b-631ec0a69a45`), by Claude, 2026-09-05.

Proof: submission `67b5cb36-254f-5a1b-99ed-935bbd484158`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $F$ be an algebraically closed field of characteristic zero and let $W$ be an affine Weierstrass
curve over $F$ that is elliptic, equipped with three pieces of structure: a `GenusOnePlaceGate`,
that is a bijection between the group $W(F)$ of points `W.Point` and the set of places of the
function field $F(W)$ together with the assertion that every such place has degree $1$; the
centredness property `GenusOnePlaceGate.IsCentred`, saying that for each nonsingular affine point
$(x,y)$ the images in $F(W)$ of the coordinate-ring classes of $X - x$ and $Y - y$ lie in the
nonunits of the valuation subring of the place attached to that point; and `AbelTheorem`, saying
that a divisor of degree $0$ on $F(W)$ is principal exactly when the sum of its points in $W(F)$ is
$0$. Assume further that for every isogeny endomorphism datum $D$ of $W$ — a structure consisting of
an $F$-algebra map $\iota : F(W) \to F(W)$ which is integral as a ring homomorphism, together with
the finiteness of $F(W)$ as a module over itself along $\iota$ — the pushforward norm formula holds
along $\iota$: for every nonzero $f \in F(W)$, every divisor whose multiplicity at each place $w$ is
$\mathrm{ord}_w(f)$, and every place $v$, the pushforward divisor has multiplicity
$\mathrm{ord}_v(\mathrm{Norm}(f))$ at $v$. Then for each such datum $D$, writing $\varphi$ for the
induced additive endomorphism `D.pointEnd` of $W(F)$ obtained from $\iota$ by pushforward of divisor
classes, there exist an additive endomorphism $\hat\varphi$ of $W(F)$ and integers $t$, $n$ with
$\varphi + \hat\varphi = t$, $\varphi\hat\varphi = \hat\varphi\varphi = n$ as endomorphisms of
$W(F)$, such that $\hat\varphi$ lies in the subring of $\mathrm{End}(W(F))$ generated by the
endomorphisms attached to all isogeny endomorphism data, and $n$ equals the $F(W)$-dimension of
$F(W)$ taken along $\iota$.

This is the existence of the dual isogeny in the function-field presentation of endomorphisms of an
elliptic curve: $\hat\varphi\varphi = \varphi\hat\varphi = [\deg\varphi]$ and $\varphi + \hat\varphi
\in \mathbb{Z}$, with the dual again lying in the subring generated by the endomorphisms coming from
isogeny data. It supplies the dual-and-trace input for
[`WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`]
(thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.
exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq),
where the degree form on the endomorphism ring is shown to satisfy the expected quadratic
inequality.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean

<!-- Generated by add_prove2me_provenance.py -->
-/


section privateSection

open WeierstrassCurve Affine AlgebraicCurve Polynomial
  ModularCurve AddMonoidHom AddMonoid.End IsDedekindDomain WithZero IsLocalRing



noncomputable section

namespace WeierstrassCurve
namespace Affine

scoped instance instHasPrincipalDivisorsFunctionField_s13 {F : Type*} [Field F] [CharZero F]
    {W : Affine F} : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField W

end Affine
end WeierstrassCurve

namespace WeierstrassCurve

private theorem nonempty_pointTorsionBy_zmod {K : Type*} [Field K]
    [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (Submodule.torsionBy ℤ W.toAffine.Point (n : ℤ) ≃+ (Fin 2 → ZMod n)) := by
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have h := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) W hn0
  have hW : WeierstrassCurve.Affine.baseChange W K = W.toAffine := by
    rw [WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id]
  rw [hW] at h
  obtain ⟨e⟩ := h
  exact ⟨e.symm.trans (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 => ZMod n)).toAddEquiv.symm⟩

end WeierstrassCurve

section

namespace ModularCurve

section KernelCardEngine

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable (W : WeierstrassCurve K) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

omit [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W] in
theorem cmm5_dp_natCard_ker_natCast (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (AddMonoidHom.ker ((n : ℤ) : AddMonoid.End W.toAffine.Point)) = n ^ 2 := by
  obtain ⟨e⟩ := W.nonempty_pointTorsionBy_zmod hn
  have : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hsets : ∀ x : W.toAffine.Point,
      x ∈ AddMonoidHom.ker ((n : ℤ) : AddMonoid.End W.toAffine.Point)
        ↔ x ∈ Submodule.torsionBy ℤ W.toAffine.Point (n : ℤ) := by
    intro x
    exact AddMonoidHom.mem_ker.trans (Submodule.mem_torsionBy_iff (n : ℤ) x).symm
  calc Nat.card (AddMonoidHom.ker ((n : ℤ) : AddMonoid.End W.toAffine.Point))
      = Nat.card (Submodule.torsionBy ℤ W.toAffine.Point (n : ℤ)) :=
        Nat.card_congr (Equiv.subtypeEquivRight hsets)
    _ = Nat.card (Fin 2 → ZMod n) := Nat.card_congr e.toEquiv
    _ = n ^ 2 := by
        rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

end KernelCardEngine
end ModularCurve
end

section

namespace ModularCurve

universe u

section Lagrange

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem cmm14_dex_card_ker_zsmul_eq_zero (φ : A →+ B) {a : A} (ha : φ a = 0) :
    (Nat.card (AddMonoidHom.ker φ) : ℤ) • a = 0 := by
  have hmem : a ∈ AddMonoidHom.ker φ := AddMonoidHom.mem_ker.mpr ha
  have hcoe : (AddMonoidHom.ker φ).subtype
      (Nat.card (AddMonoidHom.ker φ) • (⟨a, hmem⟩ : AddMonoidHom.ker φ)) = 0 := by
    rw [card_nsmul_eq_zero', _root_.map_zero]
  rw [map_nsmul, AddSubgroup.subtype_apply] at hcoe
  rw [natCast_zsmul]
  exact hcoe

end Lagrange
end ModularCurve
end

section

namespace WeierstrassCurve
namespace Affine
universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

namespace IsogenyEndDatum

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem isIntegral_algHomId :
    (AlgHom.id F W.FunctionField).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ Function.surjective_id

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem finiteAlong_algHomId : FiniteAlong F (AlgHom.id F W.FunctionField) := by
  unfold FiniteAlong algebraAlong
  exact Module.Finite.self _

def idDatum : IsogenyEndDatum W where
  ι := AlgHom.id F W.FunctionField
  hι := isIntegral_algHomId W
  hfin := finiteAlong_algHomId W

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem restrictAlong_algHomId (w : AlgebraicCurve.Place F W.FunctionField) :
    w.restrictAlong (AlgHom.id F W.FunctionField) (isIntegral_algHomId W) = w :=
  AlgebraicCurve.Place.ext (SetLike.ext fun _ => Iff.rfl)

omit [GenusOnePlaceGate.IsCentred W] in
omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
theorem idDatum_pointEnd : (idDatum W).pointEnd' = 1 := by
  refine AddMonoidHom.ext fun P => ?_
  exact (idDatum W).pointEnd'_eq_of_seam id rfl (fun Q => restrictAlong_algHomId W _) P

end IsogenyEndDatum

namespace IsogenyEndDatum

variable {W}

private def degree (D : IsogenyEndDatum W) :
    ℕ := finrankAlong F D.ι

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem degree_idDatum : (idDatum W).degree = 1 := by
  unfold degree idDatum finrankAlong algebraAlong
  exact Module.finrank_self _

end IsogenyEndDatum
end Affine
end WeierstrassCurve

end

section

section

namespace ModularCurve
namespace Es1a1

section InstanceWorld

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

omit [HasPrincipalDivisors K F'] in
theorem es1a1_dual_inertiaDeg_eq_one (hdegF : ∀ v : Place K F, v.deg = 1)
    (hdegF' : ∀ w : Place K F', w.deg = 1) (w : Place K F') :
    w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rwa [hdegF (w.restrict F), hdegF' w, one_mul] at h

theorem es1a1_dual_sum_ramificationIndex [FundamentalIdentity K F F']
    (hdegF : ∀ v : Place K F, v.deg = 1) (hdegF' : ∀ w : Place K F', w.deg = 1)
    (v : Place K F) :
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) = (Module.finrank F F' : ℤ) := by
  have h := FundamentalIdentity.sum_ramificationIndex_mul_deg
    (K := K) (F := F) (F' := F') v
  simp only [hdegF', hdegF, Nat.cast_one, mul_one] at h
  exact h

theorem es1a1_dual_pushforward_pullback_single [FundamentalIdentity K F F']
    (hdegF : ∀ v : Place K F, v.deg = 1) (hdegF' : ∀ w : Place K F', w.deg = 1)
    (v : Place K F) (n : ℤ) :
    Divisor.pushforward F (Divisor.pullback F' (Finsupp.single v n))
      = Finsupp.single v ((Module.finrank F F' : ℤ) * n) := by
  rw [Divisor.pullback_single, map_sum]
  calc ∑ w ∈ v.fiber F',
        Divisor.pushforward F (Finsupp.single w (n * w.ramificationIndex F))
      = ∑ w ∈ v.fiber F', Finsupp.single v (n * (w.ramificationIndex F : ℤ)) :=
        Finset.sum_congr rfl fun w hw => by
          rw [Divisor.pushforward_single, Place.mem_fiber.mp hw,
            es1a1_dual_inertiaDeg_eq_one hdegF hdegF' w, Nat.cast_one, mul_one]
    _ = Finsupp.single v ((Module.finrank F F' : ℤ) * n) := by
        rw [← Finsupp.single_finsetSum, ← Finset.mul_sum,
          es1a1_dual_sum_ramificationIndex hdegF hdegF' v, mul_comm]

theorem es1a1_dual_pushforward_pullback [FundamentalIdentity K F F']
    (hdegF : ∀ v : Place K F, v.deg = 1) (hdegF' : ∀ w : Place K F', w.deg = 1)
    (D : Divisor K F) :
    Divisor.pushforward F (Divisor.pullback F' D)
      = (Module.finrank F F' : ℤ) • D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, smul_add, ih,
      es1a1_dual_pushforward_pullback_single hdegF hdegF' v n,
      Finsupp.smul_single, smul_eq_mul]

end InstanceWorld

section Conorm

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]
variable (ι : W.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

def es1a1_conormDegZero (hFI : FundamentalIdentityAlong F ι hι) :
    Divisor.degZero (K := F) (F := W.FunctionField) →+
      Divisor.degZero (K := F) (F := W.FunctionField) :=
  ((Divisor.pullbackAlong ι hι).domRestrict
    (Divisor.degZero (K := F) (F := W.FunctionField))).codRestrict _
    (fun D => Divisor.pullbackAlong_mem_degZero ι hι hFI D.2)

omit [DecidableEq F] [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] [W.GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
@[scoped simp]
theorem es1a1_coe_conormDegZero (hFI : FundamentalIdentityAlong F ι hι)
    (D : Divisor.degZero (K := F) (F := W.FunctionField)) :
    (es1a1_conormDegZero ι hι hFI D : Divisor F W.FunctionField)
      = Divisor.pullbackAlong ι hι (D : Divisor F W.FunctionField) :=
  rfl

def es1a1_conormPic0Hom (hFI : FundamentalIdentityAlong F ι hι) :
    Pic0 F W.FunctionField →+ Pic0 F W.FunctionField :=
  QuotientAddGroup.map _ _ (es1a1_conormDegZero ι hι hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong ι hι hD)

omit [DecidableEq F] [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] [W.GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem es1a1_conormPic0Hom_mk (hFI : FundamentalIdentityAlong F ι hι)
    (D : Divisor.degZero (K := F) (F := W.FunctionField)) :
    es1a1_conormPic0Hom ι hι hFI (Pic0.mk D)
      = Pic0.mk (es1a1_conormDegZero ι hι hFI D) :=
  rfl

omit [DecidableEq F] [IsAlgClosed F] [WeierstrassCurve.IsElliptic W]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem es1a1_dual_pushforwardAlong_pullbackAlong
    (hFI : FundamentalIdentityAlong F ι hι) (D : Divisor F W.FunctionField) :
    Divisor.pushforwardAlong ι hι (Divisor.pullbackAlong ι hι D)
      = (finrankAlong F ι : ℤ) • D := by
  let := algebraAlong ι
  have := isScalarTower_along ι
  have := isIntegral_along ι hι
  have : FundamentalIdentity F W.FunctionField W.FunctionField := hFI
  exact es1a1_dual_pushforward_pullback (deg_eq_one (W := W)) (deg_eq_one (W := W)) D

omit [DecidableEq F] [IsAlgClosed F] [WeierstrassCurve.IsElliptic W]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem es1a1_dual_pushforwardAlongHom_conormPic0Hom
    (hFI : FundamentalIdentityAlong F ι hι) (hfin : FiniteAlong F ι)
    (hN : NormFormulaAlong F ι hfin) (c : Pic0 F W.FunctionField) :
    Pic0.pushforwardAlongHom ι hι hfin hN (es1a1_conormPic0Hom ι hι hFI c)
      = (finrankAlong F ι : ℤ) • c := by
  refine QuotientAddGroup.induction_on c fun E => ?_
  change Pic0.pushforwardAlongHom ι hι hfin hN
      (es1a1_conormPic0Hom ι hι hFI (Pic0.mk E))
    = (finrankAlong F ι : ℤ) • Pic0.mk E
  have hd : Pic0.pushforwardAlongDegZero ι hι (es1a1_conormDegZero ι hι hFI E)
      = (finrankAlong F ι : ℤ) • E := by
    refine Subtype.ext ?_
    rw [Pic0.coe_pushforwardAlongDegZero, es1a1_coe_conormDegZero,
      es1a1_dual_pushforwardAlong_pullbackAlong ι hι hFI]
    exact (map_zsmul ((Divisor.degZero (K := F) (F := W.FunctionField)).subtype)
      _ _).symm
  rw [es1a1_conormPic0Hom_mk, Pic0.pushforwardAlongHom_mk, hd]
  exact map_zsmul (QuotientAddGroup.mk' _) _ _

def es1a1_dualPointEnd (D : IsogenyEndDatum W)
    (hFI : FundamentalIdentityAlong F D.ι D.hι) : AddMonoid.End W.Point :=
  ((genusOnePic0Equiv W).toAddMonoidHom.comp
      (es1a1_conormPic0Hom D.ι D.hι hFI)).comp
    (genusOnePic0Equiv W).symm.toAddMonoidHom

omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] [GenusOnePlaceGate.IsCentred W] in
theorem es1a1_dualPointEnd_apply (D : IsogenyEndDatum W)
    (hFI : FundamentalIdentityAlong F D.ι D.hι) (P : W.Point) :
    es1a1_dualPointEnd D hFI P
      = genusOnePic0Equiv W
          (es1a1_conormPic0Hom D.ι D.hι hFI ((genusOnePic0Equiv W).symm P)) :=
  rfl

omit [GenusOnePlaceGate.IsCentred W] in
omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
theorem es1a1_pointEnd_mul_dualPointEnd (D : IsogenyEndDatum W)
    (hFI : FundamentalIdentityAlong F D.ι D.hι) :
    D.pointEnd' * es1a1_dualPointEnd D hFI
      = ((finrankAlong F D.ι : ℤ) : AddMonoid.End W.Point) := by
  refine DFunLike.ext _ _ fun P => ?_
  change D.pointEnd' (es1a1_dualPointEnd D hFI P)
      = ((finrankAlong F D.ι : ℤ) : AddMonoid.End W.Point) P
  rw [AddMonoid.End.intCast_apply, IsogenyEndDatum.pointEnd'_apply,
    es1a1_dualPointEnd_apply, ← genusOnePic0Equiv_symm_apply,
    AddEquiv.symm_apply_apply,
    es1a1_dual_pushforwardAlongHom_conormPic0Hom D.ι D.hι hFI D.hfin
      (normFormulaAlong_of_elliptic D.ι D.hfin), map_zsmul,
    AddEquiv.apply_symm_apply]

end Conorm
end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Es1a1

section AddMulAlgebra

variable {A : Type*} [AddCommGroup A]

def es1a4_twDualEndData_of_add_of_mul (φ ψ : AddMonoid.End A) (t n : ℤ)
    (hadd : φ + ψ = (t : AddMonoid.End A)) (hmul : φ * ψ = (n : AddMonoid.End A)) :
    DualEndData φ where
  dual := ψ
  trace := t
  norm := n
  add_dual := hadd
  mul_dual := hmul
  dual_mul := by
    have hψ : ψ = (t : AddMonoid.End A) - φ := eq_sub_of_add_eq' hadd
    have hc : (t : AddMonoid.End A) * φ = φ * (t : AddMonoid.End A) :=
      (Int.cast_commute t φ).eq
    rw [hψ, sub_mul, hc, ← mul_sub, ← hψ, hmul]

end AddMulAlgebra
end Es1a1
end ModularCurve
end
end

section

namespace AlgebraicCurve
attribute [local instance 0] Place.valuationSubringAlgebra

section Producer

variable {K F Z : Type*} [Field K] [Field F] [Field Z]
  [Algebra K F] [Algebra K Z] [Algebra F Z] [IsScalarTower K F Z]
  [FiniteDimensional F Z] [Algebra.IsSeparable F Z]
  [HasPrincipalDivisors K Z]

variable (E : IntermediateField F Z)

def IntegralAt (v : Place K F) (q : Polynomial F) : Prop :=
  ∀ i, q.coeff i ∈ v.toValuationSubring

theorem mem_lifts_of_integralAt {v : Place K F} {q : Polynomial F}
    (hq : IntegralAt v q) :
    q ∈ Polynomial.lifts (algebraMap v.toValuationSubring F) :=
  (Polynomial.lifts_iff_coeff_lifts q).mpr fun n => ⟨⟨q.coeff n, hq n⟩, rfl⟩

end Producer
end AlgebraicCurve
end

section

section

namespace WeierstrassCurve
namespace Affine
universe u

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [W.GenusOnePlaceGate]

@[scoped simp] theorem placeOfPointEquiv_symm_placeOfPoint (P : W.Point) :
    (placeOfPointEquiv W).symm (placeOfPoint P) = P :=
  (placeOfPointEquiv W).symm_apply_apply P

end Affine
end WeierstrassCurve
end

section

namespace WeierstrassCurve
namespace Affine
universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

namespace IsogenyEndDatum

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem isIntegral_comp (D₁ D₂ : IsogenyEndDatum W) :
    (D₂.ι.comp D₁.ι).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans D₁.ι.toRingHom D₂.ι.toRingHom D₁.hι D₂.hι

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem finiteAlong_comp (D₁ D₂ : IsogenyEndDatum W) :
    FiniteAlong F (D₂.ι.comp D₁.ι) :=
  RingHom.Finite.comp (g := D₂.ι.toRingHom) (f := D₁.ι.toRingHom) D₂.hfin D₁.hfin

def compDatum (D₁ D₂ : IsogenyEndDatum W) : IsogenyEndDatum W where
  ι := D₂.ι.comp D₁.ι
  hι := isIntegral_comp W D₁ D₂
  hfin := finiteAlong_comp W D₁ D₂

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
@[scoped simp] theorem compDatum_ι (D₁ D₂ : IsogenyEndDatum W) :
    (compDatum W D₁ D₂).ι = D₂.ι.comp D₁.ι := rfl

end IsogenyEndDatum

end Affine
end WeierstrassCurve
end

section

namespace AlgebraicCurve
section Identity

variable (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

def RamificationInertiaIdentity : Prop :=
  ∀ (v : Place K F) (s : Finset (Place K F')), (∀ w : Place K F', w ∈ s ↔ w.restrict F = v) →
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ)

variable {K F F'}

theorem fundamentalIdentity_iff_ramificationInertiaIdentity [HasPrincipalDivisors K F'] :
    FundamentalIdentity K F F' ↔ RamificationInertiaIdentity K F F' := by
  constructor
  · intro H v s hs
    have hseq : s = v.fiber F' := by
      ext w
      rw [hs w, Place.mem_fiber]
    rw [hseq]
    exact H.sum_ramificationIndex_mul_deg v
  · intro H
    exact ⟨fun v => H v (v.fiber F') fun w => Place.mem_fiber⟩

end Identity

end AlgebraicCurve
end

section

open WithZero
open scoped Polynomial

namespace AlgebraicCurve
theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le
  · rw [← exp_log hx0] at hx ⊢
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

namespace Place
open AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_eq_neg_log_of_valuationSubring_eq (w : Valuation F ℤᵐ⁰)
    (hw : w.valuationSubring = v.toValuationSubring) {π : F} (hπ : w π = exp (-1 : ℤ))
    {f : F} (hf : f ≠ 0) : v.ord f = -log (w f) := by
  have hequiv : w.IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hw
  have hexp_lt : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl]
    exact exp_lt_exp.mpr (by omega)
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hadic_π₀ : v.adicValuation (π₀ : F) = exp (-1 : ℤ) := v.adicValuation_coe_irreducible hπ₀
  have hwπ₀ : w (π₀ : F) = exp (-1 : ℤ) := by
    refine le_antisymm (le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mpr ?_)) ?_
    · rw [hadic_π₀]
      exact hexp_lt
    · rw [← hπ]
      refine (hequiv π π₀).mpr ?_
      rw [hadic_π₀]
      refine le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mp ?_)
      rw [hπ]
      exact hexp_lt
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ₀
  have hwu : w ((u : v.toValuationSubring) : F) = 1 :=
    hequiv.eq_one_iff_eq_one.mpr ((v.adicValuation_coe_eq_one_iff _).mpr u.isUnit)
  set n := v.ord f with hn
  rw [hu, map_mul, map_zpow₀, hwu, hwπ₀, one_mul, log_zpow, log_exp, smul_eq_mul]
  ring

end Place

end AlgebraicCurve
end

section

namespace AlgebraicCurve
section FinrankAlongComp

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
variable [Algebra K F] [Algebra K F'] [Algebra K F'']

theorem finrankAlong_comp (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'') :
    finrankAlong K (ψ.comp φ) = finrankAlong K φ * finrankAlong K ψ := by
  let iφ : Algebra F F' := algebraAlong φ
  let iψ : Algebra F' F'' := algebraAlong ψ
  let iψφ : Algebra F F'' := algebraAlong (ψ.comp φ)
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank F F' F'').symm

end FinrankAlongComp
end AlgebraicCurve

end

section

namespace ModularCurve

section DegreeLayer

universe u

theorem cmm10_deg_finrankAlong_pos {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) :
    0 < finrankAlong K φ := by
  let := algebraAlong φ
  have hfin' : Module.Finite F F' := hfin
  exact (Module.finrank_pos_iff_of_free (R := F) (M := F')).mpr inferInstance

variable {F : Type u} [Field F] {W : Affine F}

theorem cmm10_deg_degree_pos (D : IsogenyEndDatum W) : 0 < D.degree :=
  cmm10_deg_finrankAlong_pos D.ι D.hfin

end DegreeLayer

section DatumLayerFaces

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]

def cmm10_deg_DatumKernelDegreeFace (W : Affine F) [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]
    :
    Prop :=
  ∀ D : IsogenyEndDatum W,
    Nat.card (AddMonoidHom.ker D.pointEnd') = D.degree

end DatumLayerFaces
end ModularCurve
end

section

section

namespace WeierstrassCurve
namespace Affine
universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

namespace IsogenyEndDatum

omit [DecidableEq F] [IsAlgClosed F] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_ipfd_mem_fiberAlong_placeOfPoint_iff (D : IsogenyEndDatum W)
    (P Q : W.Point) :
    placeOfPoint P ∈ Place.fiberAlong D.ι D.hι (placeOfPoint Q)
      ↔ D.geomMorph P = Q := by
  have _pin := Classical.em True
  rw [Place.mem_fiberAlong, D.placeOfPoint_geomMorph P]
  exact ⟨fun h => placeOfPoint_injective h, fun h => h ▸ rfl⟩

omit [IsAlgClosed F] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_ipfd_pullbackAlong_single_placeOfPoint_apply (D : IsogenyEndDatum W)
    (Q P : W.Point) :
    (Divisor.pullbackAlong D.ι D.hι (Finsupp.single (placeOfPoint Q) 1))
        (placeOfPoint P)
      = if D.geomMorph P = Q
          then ((placeOfPoint P).ramificationIndexAlong D.ι : ℤ) else 0 := by
  have _pin := Classical.em True
  classical
  rw [Divisor.pullbackAlong_single D.ι D.hι (placeOfPoint Q) 1]
  simp only [one_mul, Finset.sum_apply', Finsupp.single_apply]
  rw [Finset.sum_ite_eq' (Place.fiberAlong D.ι D.hι (placeOfPoint Q))
    (placeOfPoint P) (fun w => (w.ramificationIndexAlong D.ι : ℤ))]
  by_cases hm : D.geomMorph P = Q
  · rw [ite_eq_left ((kw_ipfd_mem_fiberAlong_placeOfPoint_iff D P Q).mpr hm),
      ite_eq_left hm]
  · rw [ite_eq_right (fun h => hm ((kw_ipfd_mem_fiberAlong_placeOfPoint_iff D P Q).mp h)),
      ite_eq_right hm]

abbrev kw_ipfd_unramified (D : IsogenyEndDatum W) : Prop :=
  ∀ P : W.Point, (placeOfPoint P).ramificationIndexAlong D.ι = 1

omit [IsAlgClosed F] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_ipfd_pullbackAlong_single_placeOfPoint_apply_of_unramified
    (D : IsogenyEndDatum W) (hunr : kw_ipfd_unramified D) (Q P : W.Point) :
    (Divisor.pullbackAlong D.ι D.hι (Finsupp.single (placeOfPoint Q) 1))
        (placeOfPoint P)
      = if D.geomMorph P = Q then 1 else 0 := by
  have _pin := Classical.em True
  rw [kw_ipfd_pullbackAlong_single_placeOfPoint_apply D Q P, hunr P,
    Nat.cast_one]

end IsogenyEndDatum
end Affine
end WeierstrassCurve
end
end

section

section

namespace ModularCurve
namespace Es1a1

section CompositionLaw

universe u

variable {F : Type u} [Field F] [DecidableEq F]
variable {W : Affine F} [WeierstrassCurve.Affine.GenusOnePlaceGate W] [W.AbelTheorem]

omit [DecidableEq F] [W.AbelTheorem] in
theorem es1a3_pushforwardAlong_comp
    (φ ψ : W.FunctionField →ₐ[F] W.FunctionField)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hcomp : (ψ.comp φ).toRingHom.IsIntegral)
    (D : Divisor F W.FunctionField) :
    Divisor.pushforwardAlong (ψ.comp φ) hcomp D
      = Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong ψ hψ D) := by
  induction D using Finsupp.induction with
  | zero => simp only [_root_.map_zero]
  | single_add w n D _ _ ih =>
    rw [map_add, map_add, map_add, ih, pushforwardAlong_single_eq (ψ.comp φ) hcomp,
      pushforwardAlong_single_eq ψ hψ, pushforwardAlong_single_eq φ hφ,
      Place.restrictAlong_comp φ ψ hφ hψ hcomp]

omit [DecidableEq F] [W.AbelTheorem] in
theorem es1a3_pushforwardAlongHom_comp
    (φ ψ : W.FunctionField →ₐ[F] W.FunctionField)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hcomp : (ψ.comp φ).toRingHom.IsIntegral)
    (hφfin : FiniteAlong F φ) (hψfin : FiniteAlong F ψ)
    (hcfin : FiniteAlong F (ψ.comp φ))
    (hφN : NormFormulaAlong F φ hφfin) (hψN : NormFormulaAlong F ψ hψfin)
    (hcN : NormFormulaAlong F (ψ.comp φ) hcfin)
    (c : Pic0 F W.FunctionField) :
    Pic0.pushforwardAlongHom (ψ.comp φ) hcomp hcfin hcN c
      = Pic0.pushforwardAlongHom φ hφ hφfin hφN
          (Pic0.pushforwardAlongHom ψ hψ hψfin hψN c) := by
  refine QuotientAddGroup.induction_on c fun E => ?_
  change Pic0.pushforwardAlongHom (ψ.comp φ) hcomp hcfin hcN (Pic0.mk E)
      = Pic0.pushforwardAlongHom φ hφ hφfin hφN
          (Pic0.pushforwardAlongHom ψ hψ hψfin hψN (Pic0.mk E))
  rw [Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk,
    Pic0.pushforwardAlongHom_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  simp only [Pic0.coe_pushforwardAlongDegZero]
  exact es1a3_pushforwardAlong_comp φ ψ hφ hψ hcomp E

theorem es1a3_pointClass_genusOnePic0Equiv (c : Pic0 F W.FunctionField) :
    pointClass (genusOnePic0Equiv W c) = c := by
  rw [← genusOnePic0Equiv_symm_apply, AddEquiv.symm_apply_apply]

theorem es1a3_compDatum_pointEnd [CharZero F] (D₁ D₂ : IsogenyEndDatum W) :
    (IsogenyEndDatum.compDatum W D₁ D₂).pointEnd' = D₁.pointEnd' * D₂.pointEnd' := by
  refine AddMonoidHom.ext fun P => ?_
  change (IsogenyEndDatum.compDatum W D₁ D₂).pointEnd' P = D₁.pointEnd' (D₂.pointEnd' P)
  rw [IsogenyEndDatum.pointEnd'_apply, IsogenyEndDatum.pointEnd'_apply,
    IsogenyEndDatum.pointEnd'_apply, es1a3_pointClass_genusOnePic0Equiv]
  exact congrArg (genusOnePic0Equiv W)
    (es1a3_pushforwardAlongHom_comp D₁.ι D₂.ι D₁.hι D₂.hι
      (IsogenyEndDatum.compDatum W D₁ D₂).hι D₁.hfin D₂.hfin
      (IsogenyEndDatum.compDatum W D₁ D₂).hfin
      (normFormulaAlong_of_elliptic D₁.ι D₁.hfin)
      (normFormulaAlong_of_elliptic D₂.ι D₂.hfin)
      (normFormulaAlong_of_elliptic (IsogenyEndDatum.compDatum W D₁ D₂).ι
        (IsogenyEndDatum.compDatum W D₁ D₂).hfin)
      (pointClass P))

end CompositionLaw
end Es1a1
end ModularCurve
end
end

section

namespace AlgebraicCurve
attribute [local instance 0] Place.valuationSubringAlgebra

section PolarLocus

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

theorem finite_setOf_ord_ne_zero_of_hasPrincipalDivisors {f : F} (hf : f ≠ 0) :
    {v : Place K F | v.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine D.support.finite_toSet.subset fun v hv => Finsupp.mem_support_iff.mpr ?_
  rw [hD v]
  exact hv

theorem finite_setOf_notMem_toValuationSubring (f : F) :
    {v : Place K F | f ∉ v.toValuationSubring}.Finite := by
  rcases eq_or_ne f 0 with rfl | hf
  · refine Set.finite_empty.subset fun v hv => ?_
    exact absurd (v.toValuationSubring.zero_mem) hv
  · refine (finite_setOf_ord_ne_zero_of_hasPrincipalDivisors (K := K) hf).subset
      fun v hv => ?_
    intro h0
    exact hv (AlgebraicCurve.Place.mem_of_ord_nonneg v hf h0.ge)

end PolarLocus
end AlgebraicCurve
end

section

open scoped Polynomial.Bivariate

namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_algebraMap_s18priv (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]
    exact v.algebraMap_mem' c⁻¹
  have h1 := AlgebraicCurve.Place.ord_nonneg_of_mem v hmem
  have h2 := AlgebraicCurve.Place.ord_nonneg_of_mem v hmem'
  rw [v.ord_inv] at h2
  omega

private theorem ord_pow (f : F) (n : ℕ) :
    v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

private theorem ord_ringHom_eq_natDegree_mul {φ : K[X] →+* F}
    (hφinj : Function.Injective φ)
    (hφC : ∀ c : K, φ (C c) = algebraMap K F c) (hz : v.ord (φ X) < 0) :
    ∀ {p : K[X]}, p ≠ 0 → v.ord (φ p) = p.natDegree * v.ord (φ X) := by
  have hX0 : φ X ≠ 0 := fun h => by simp [Place.ord, h] at hz
  have hmono : ∀ (c : K) (n : ℕ), c ≠ 0 → v.ord (φ (C c * X ^ n)) = n * v.ord (φ X) := by
    intro c n hc
    have hc0 : φ (C c) ≠ 0 := by
      rw [hφC]
      simpa using hc
    rw [map_mul, map_pow, v.ord_mul hc0 (pow_ne_zero n hX0), hφC,
      AlgebraicCurve.Place.ord_algebraMap v,
      v.ord_pow, zero_add]
  intro p
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    intro hp
    subst hd
    rcases eq_or_ne p.eraseLead 0 with he | he
    · conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow, he, zero_add]
      exact hmono _ _ (leadingCoeff_ne_zero.mpr hp)
    · have hlt : p.eraseLead.natDegree < p.natDegree := by
        rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
        · exact h
        · exact absurd h he
      have hIH : v.ord (φ p.eraseLead) = p.eraseLead.natDegree * v.ord (φ X) :=
        ih _ hlt rfl he
      have hlead : v.ord (φ (C p.leadingCoeff * X ^ p.natDegree))
          = p.natDegree * v.ord (φ X) := hmono _ _ (leadingCoeff_ne_zero.mpr hp)
      have hcast : (p.eraseLead.natDegree : ℤ) < (p.natDegree : ℤ) := by exact_mod_cast hlt
      have hne : v.ord (φ p.eraseLead) ≠ v.ord (φ (C p.leadingCoeff * X ^ p.natDegree)) := by
        rw [hIH, hlead]
        nlinarith
      have he2 : φ (C p.leadingCoeff * X ^ p.natDegree) ≠ 0 := fun hcon =>
        mul_ne_zero (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)) (pow_ne_zero _ X_ne_zero)
          (hφinj (hcon.trans (_root_.map_zero φ).symm))
      have he1 : φ p.eraseLead ≠ 0 := fun hcon => he (hφinj (hcon.trans (_root_.map_zero φ).symm))
      conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow]
      rw [map_add, v.ord_add_eq_min he1 he2 hne, hIH, hlead]
      have h1 : (p.natDegree : ℤ) * v.ord (φ X) ≤ (p.eraseLead.natDegree : ℤ) * v.ord (φ X) := by
        nlinarith
      omega

private theorem le_ord_ringHom_of_natDegree_le {φ : K[X] →+* F}
    (hφinj : Function.Injective φ)
    (hφC : ∀ c : K, φ (C c) = algebraMap K F c) (hz : v.ord (φ X) < 0)
    {p : K[X]} {d : ℕ} (hd : p.natDegree ≤ d) :
    (d : ℤ) * v.ord (φ X) ≤ v.ord (φ p) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [_root_.map_zero, Place.ord_zero]
    nlinarith [hz]
  rw [v.ord_ringHom_eq_natDegree_mul hφinj hφC hz hp]
  have h1 : (p.natDegree : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  nlinarith

end Place
end AlgebraicCurve

namespace WeierstrassCurve
namespace Affine
open WeierstrassCurve.Affine.CoordinateRing
open WeierstrassCurve.Affine.CoordinateRing
variable {F : Type*} [Field F] {W : Affine F}

theorem natDegree_norm_smul_basis_left {p : F[X]} (hp : p ≠ 0) :
    ((Algebra.norm F[X] (p • (1 : W.CoordinateRing)
        + (0 : F[X]) • CoordinateRing.mk W Y)).natDegree : ℤ) = 2 * p.natDegree := by
  have hdeg := degree_norm_smul_basis (W' := W) p 0
  rw [Polynomial.degree_zero, show (2 : ℕ) • (⊥ : WithBot ℕ) + 3 = ⊥ by
      rw [two_nsmul]; simp, max_eq_left bot_le, Polynomial.degree_eq_natDegree hp, two_nsmul,
    ← Nat.cast_add] at hdeg
  rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  push_cast
  ring

theorem natDegree_norm_smul_basis_right {q : F[X]} (hq : q ≠ 0) :
    ((Algebra.norm F[X] ((0 : F[X]) • (1 : W.CoordinateRing)
        + q • CoordinateRing.mk W Y)).natDegree : ℤ) = 2 * q.natDegree + 3 := by
  have hdeg := degree_norm_smul_basis (W' := W) 0 q
  rw [Polynomial.degree_zero, show (2 : ℕ) • (⊥ : WithBot ℕ) = ⊥ by
      rw [two_nsmul]; simp, max_eq_right bot_le, Polynomial.degree_eq_natDegree hq, two_nsmul,
    ← Nat.cast_add, show ((3 : WithBot ℕ)) = ((3 : ℕ) : WithBot ℕ) from rfl,
    ← Nat.cast_add] at hdeg
  rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  push_cast
  ring

theorem natDegree_norm_smul_basis_max {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ((Algebra.norm F[X] (p • (1 : W.CoordinateRing)
        + q • CoordinateRing.mk W Y)).natDegree : ℤ)
      = max (2 * (p.natDegree : ℤ)) (2 * (q.natDegree : ℤ) + 3) := by
  have hdeg := degree_norm_smul_basis (W' := W) p q
  rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq, two_nsmul,
    two_nsmul, ← Nat.cast_add, ← Nat.cast_add,
    show ((3 : WithBot ℕ)) = ((3 : ℕ) : WithBot ℕ) from rfl, ← Nat.cast_add] at hdeg
  rcases le_total (q.natDegree + q.natDegree + 3) (p.natDegree + p.natDegree) with h | h
  · rw [max_eq_left (by exact_mod_cast h)] at hdeg
    rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
    push_cast
    omega
  · rw [max_eq_right (by exact_mod_cast h)] at hdeg
    rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
    push_cast
    omega

variable (v : AlgebraicCurve.Place F W.FunctionField)

theorem two_mul_ord_Y_eq_three_mul_ord_X (hv : ¬ IsFinitePlace v) :
    2 * v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
      = 3 * v.ord (polyToFunctionField W X) := by
  set η := algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) with hηdef
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hη0 : η ≠ 0 := Y_image_ne_zero
  set c₁ : F[X] := C W.a₁ * X + C W.a₃ with hc₁def
  set cb : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ with hcbdef
  have hrel : η * η = polyToFunctionField W cb - polyToFunctionField W c₁ * η := by
    have h1 := smul_basis_mul_Y (W' := W) 0 1
    rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at h1
    have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) h1
    rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
    exact h2
  have hrelL : (η + polyToFunctionField W c₁) * η = polyToFunctionField W cb := by
    rw [add_mul]
    linear_combination hrel
  have hcbdeg : cb.natDegree = 3 := by
    rw [hcbdef, ← one_mul (X ^ 3 : F[X]), ← C_1]
    exact Polynomial.natDegree_cubic one_ne_zero
  have hcb0 : cb ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hcbdeg
    exact absurd hcbdeg (by norm_num)
  have hcbord : v.ord (polyToFunctionField W cb) = 3 * v.ord (polyToFunctionField W X) := by
    rw [v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA
      hcb0, hcbdeg]
    push_cast
    ring
  have hc₁ord : (1 : ℤ) * v.ord (polyToFunctionField W X)
      ≤ v.ord (polyToFunctionField W c₁) := by
    refine v.le_ord_ringHom_of_natDegree_le polyToFunctionField_injective polyToFunctionField_C
      hA ?_
    rw [hc₁def]
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [Polynomial.natDegree_C, max_le_iff]
    refine ⟨le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp), by omega⟩
  rw [one_mul] at hc₁ord
  have hfac0 : η + polyToFunctionField W c₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrelL
    exact polyToFunctionField_ne_zero hcb0 hrelL.symm
  have hLHS : v.ord (η + polyToFunctionField W c₁) + v.ord η
      = 3 * v.ord (polyToFunctionField W X) := by
    rw [← hcbord, ← hrelL, v.ord_mul hfac0 hη0]
  rcases eq_or_ne (polyToFunctionField W c₁) 0 with hc₁0 | hc₁0
  · rw [hc₁0, add_zero] at hLHS
    omega
  · by_cases hBc : v.ord η = v.ord (polyToFunctionField W c₁)
    · exfalso
      have hmin : min (v.ord η) (v.ord (polyToFunctionField W c₁))
          ≤ v.ord (η + polyToFunctionField W c₁) := v.min_ord_le_ord_add' hfac0
      rw [← hBc, min_self] at hmin
      have hBA : v.ord (polyToFunctionField W X) ≤ v.ord η := hBc ▸ hc₁ord
      omega
    · have hsum : v.ord (η + polyToFunctionField W c₁)
          = min (v.ord η) (v.ord (polyToFunctionField W c₁)) :=
        v.ord_add_eq_min hη0 hc₁0 hBc
      rcases min_cases (v.ord η) (v.ord (polyToFunctionField W c₁)) with
        ⟨hm, hle⟩ | ⟨hm, hlt⟩ <;> rw [hm] at hsum
      · rw [hsum] at hLHS
        omega
      · exfalso
        rw [hsum] at hLHS
        omega

private theorem ne_arith {A B s t : ℤ} (hA : A < 0) (hY : 2 * B = 3 * A) :
    s * A ≠ t * A + B := by
  intro hcon
  have h4 : (2 * s - (2 * t + 3)) * A = 0 := by linear_combination 2 * hcon + hY
  rcases mul_eq_zero.mp h4 with h5 | h5
  · omega
  · omega

private theorem two_mul_min_arith {A B s t : ℤ} (hA : A < 0) (hY : 2 * B = 3 * A) :
    2 * min (s * A) (t * A + B) = A * max (2 * s) (2 * t + 3) := by
  rcases le_or_gt (2 * t + 3) (2 * s) with h | h
  · rw [max_eq_left h, min_eq_left (by nlinarith)]
    ring
  · rw [max_eq_right h.le, min_eq_right (by nlinarith)]
    linear_combination hY

theorem two_mul_ord_eq_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    {f : W.CoordinateRing} (hf : f ≠ 0) :
    2 * v.ord (algebraMap W.CoordinateRing W.FunctionField f)
      = v.ord (polyToFunctionField W X) * ((Algebra.norm F[X] f).natDegree : ℤ) := by
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hη0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) ≠ 0 :=
    Y_image_ne_zero
  have hYord := two_mul_ord_Y_eq_three_mul_ord_X v hv
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  by_cases hq : q = 0
  · subst hq
    have hp : p ≠ 0 := fun h => hf (by rw [h, zero_smul, zero_smul, add_zero])
    rw [natDegree_norm_smul_basis_left hp, algebraMap_smul_basis, _root_.map_zero, zero_mul,
      add_zero,
      v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA hp]
    ring
  · by_cases hp : p = 0
    · subst hp
      rw [natDegree_norm_smul_basis_right hq, algebraMap_smul_basis, _root_.map_zero, zero_add,
        v.ord_mul (polyToFunctionField_ne_zero hq) hη0,
        v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA hq]
      linear_combination hYord
    · rw [natDegree_norm_smul_basis_max hp hq, algebraMap_smul_basis]
      have hordp : v.ord (polyToFunctionField W p)
          = (p.natDegree : ℤ) * v.ord (polyToFunctionField W X) :=
        v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA hp
      have hordqy : v.ord (polyToFunctionField W q
            * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
          = (q.natDegree : ℤ) * v.ord (polyToFunctionField W X)
            + v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
        rw [v.ord_mul (polyToFunctionField_ne_zero hq) hη0,
          v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA
            hq]
      have hne : v.ord (polyToFunctionField W p) ≠ v.ord (polyToFunctionField W q
          * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
        rw [hordp, hordqy]
        exact ne_arith hA hYord
      have hqy0 : polyToFunctionField W q
          * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) ≠ 0 :=
        mul_ne_zero (polyToFunctionField_ne_zero hq) hη0
      rw [v.ord_add_eq_min (polyToFunctionField_ne_zero hp) hqy0 hne, hordp, hordqy]
      exact two_mul_min_arith hA hYord

theorem ord_X_eq_neg_two_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) :
    v.ord (polyToFunctionField W X) = -2 := by
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hYord := two_mul_ord_Y_eq_three_mul_ord_X v hv
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπord : v.ord (π : W.FunctionField) = 1 := v.ord_coe_irreducible hπ
  have hπ0 : (π : W.FunctionField) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing)
    (π : W.FunctionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, _root_.map_zero, zero_div] at hab
    exact hπ0 hab.symm
  have ha' : algebraMap W.CoordinateRing W.FunctionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr ha0
  have hb' : algebraMap W.CoordinateRing W.FunctionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hb0
  have h1 := two_mul_ord_eq_of_not_isFinitePlace v hv ha0
  have h2 := two_mul_ord_eq_of_not_isFinitePlace v hv hb0
  have h3 : v.ord (π : W.FunctionField)
      = v.ord (algebraMap W.CoordinateRing W.FunctionField a)
        - v.ord (algebraMap W.CoordinateRing W.FunctionField b) := by
    rw [← hab, div_eq_mul_inv, v.ord_mul ha' (inv_ne_zero hb'), v.ord_inv]
    ring
  rw [hπord] at h3
  have h4 : (2 : ℤ) = v.ord (polyToFunctionField W X) * (((Algebra.norm F[X] a).natDegree : ℤ)
      - ((Algebra.norm F[X] b).natDegree : ℤ)) := by
    linear_combination 2 * h3 + h1 - h2
  have h5 : v.ord (polyToFunctionField W X) ∣ 2 := ⟨_, h4⟩
  have h6 : (2 : ℤ) ∣ v.ord (polyToFunctionField W X) := by
    have h7 : (2 : ℤ) ∣ 3 * v.ord (polyToFunctionField W X) := ⟨_, hYord.symm⟩
    omega
  have h8 : (v.ord (polyToFunctionField W X)).natAbs ∣ (2 : ℤ).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h5
  have h9 : (2 : ℤ).natAbs ∣ (v.ord (polyToFunctionField W X)).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h6
  have h10 : (v.ord (polyToFunctionField W X)).natAbs = 2 :=
    Nat.dvd_antisymm (by simpa using h8) (by simpa using h9)
  omega

end Affine
end WeierstrassCurve
end

section

namespace AlgebraicCurve
namespace Place

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone
  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega
  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring
  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, AlgebraicCurve.Place.mem_iff_ord_nonneg w hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega
  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega
  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel
  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 0] valuationSubringAlgebra

section Setup

variable (v : Place K F)

scoped instance (priority := 100) : IsScalarTower v.toValuationSubring F F' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance : IsDedekindDomain (integralClosureAt F' v) :=
  integralClosure.isDedekindDomain v.toValuationSubring F F'

scoped instance : IsFractionRing (integralClosureAt F' v) F' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F F'

scoped instance : Module.Finite v.toValuationSubring (integralClosureAt F' v) :=
  IsIntegralClosure.finite v.toValuationSubring F F' _

scoped instance : Module.IsTorsionFree v.toValuationSubring (integralClosureAt F' v) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosureAt_injective v (by rw [h, _root_.map_zero]))
  · exact Or.inr h

end Setup

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  refine eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  · intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  · obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, _root_.map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  · intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    change 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
    have hmem : y ∈ w.toValuationSubring ↔ (fiberCenter F' v hw).valuation F' y ≤ 1 := by
      rw [toValuationSubring_eq_of_restrict_eq hw,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact Iff.rfl
    rw [hmem]
    constructor
    · intro h
      calc (fiberCenter F' v hw).valuation F' y
          = exp (log ((fiberCenter F' v hw).valuation F' y)) := (exp_log hy0).symm
        _ ≤ exp 0 := by rw [exp_le_exp]; omega
        _ = 1 := exp_zero
    · intro h
      have h1 : exp (log ((fiberCenter F' v hw).valuation F' y)) ≤ exp 0 := by
        rw [exp_log hy0, exp_zero]
        exact h
      rw [exp_le_exp] at h1
      omega

theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n := by
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hc
  rw [← neg_log_valuation_fiberCenter_eq_ord hw hcF,
    HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have h0 : (fiberCenter F' v hw).intValuation c ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ c hc
  constructor
  · intro h
    calc (fiberCenter F' v hw).intValuation c
        = exp (log ((fiberCenter F' v hw).intValuation c)) := (exp_log h0).symm
      _ ≤ exp (-(n : ℤ)) := by rw [exp_le_exp]; omega
  · intro h
    have h1 : exp (log ((fiberCenter F' v hw).intValuation c)) ≤ exp (-(n : ℤ)) := by
      rw [exp_log h0]
      exact h
    rw [exp_le_exp] at h1
    omega

theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπC : algebraMap v.toValuationSubring (integralClosureAt F' v) π ≠ 0 :=
    algebraMap_integralClosureAt_ne_zero hπ0
  have hmap : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (integralClosureAt F' v))
        = Ideal.span {algebraMap v.toValuationSubring (integralClosureAt F' v) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hord : w.ord (algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) π))
        = w.ramificationIndex F := by
    rw [ord_algebraMap_integralClosureAt hw, ValuationSubring.algebraMap_apply,
      v.ord_coe_irreducible hπ, mul_one]
  refine (Ideal.ramificationIdx'_spec ?_ ?_).symm
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
    have : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    push_cast
    omega

end ValuationDictionary

section ResidueDictionary

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

theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal := by
  ext c
  rw [RingHom.mem_ker, residueOfCenter_apply, IsLocalRing.residue_eq_zero_iff]
  exact Iff.rfl

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
      AlgebraicCurve.Place.ord_nonneg_of_mem w (forall_mem_of_restrict_eq hw s)
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
    rw [hxas, RingHom.map_sub (algebraMap (integralClosureAt F' v) F') _ _,
      map_mul (algebraMap (integralClosureAt F' v) F') (a * t) s,
      sub_mul, mul_assoc, mul_inv_cancel₀ hsF, mul_one]
  have hdiffC : a * t * s - a ≠ 0 := by
    intro h
    apply hcoene
    rw [hfactor, h, _root_.map_zero, zero_mul]
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
    (inv_ne_zero hsF), w.ord_inv, hsord, _root_.neg_zero, add_zero]
  exact (mem_fiberCenter_iff_ord_pos hw hdiffC).mp hdiffP

def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  (Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm).trans
    ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))

def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  IsLocalRing.ResidueField.mapEquiv (placeCongrEquiv hw)

end ResidueDictionary
end Place
end AlgebraicCurve
end

section

section

open FractionalIdeal
open WithZero
open scoped nonZeroDivisors
open scoped Polynomial.Bivariate

namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]
variable [Algebra K R] [Algebra K L] [IsScalarTower K R L]

theorem ord_ofHeightOneSpectrum_eq_neg_log (w : HeightOneSpectrum R) {f : L} (hf : f ≠ 0) :
    (ofHeightOneSpectrum (K := K) w).ord f = -log (w.valuation L f) := by
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hval : w.valuation L (algebraMap R L π) = exp (-1 : ℤ) := by
    rw [w.valuation_of_algebraMap]
    exact hπ
  exact AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq (ofHeightOneSpectrum (K := K) w)
    (w.valuation L) rfl hval hf

end Place
end AlgebraicCurve

end

section

namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 0] valuationSubringAlgebra

variable {v : Place K F} {w : Place K F'}

theorem ord_deriv_pos_of_ramificationIndex_ne_one
    (hw : w.restrict F = v) (θ : F')
    (hgen : IntermediateField.adjoin F {θ} = ⊤)
    (hθint : _root_.IsIntegral v.toValuationSubring θ)
    (hram : w.ramificationIndex F ≠ 1) :
    0 < w.ord (aeval θ (derivative (minpoly F θ))) := by
  obtain ⟨c, rfl⟩ : ∃ c : integralClosureAt F' v,
      algebraMap (integralClosureAt F' v) F' c = θ := ⟨⟨θ, hθint⟩, rfl⟩
  have hAc : _root_.IsIntegral v.toValuationSubring c := Algebra.IsIntegral.isIntegral c
  have hadjF : Algebra.adjoin F {algebraMap (integralClosureAt F' v) F' c} = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hgen, IntermediateField.top_toSubalgebra]
  have hmem : aeval c (derivative (minpoly v.toValuationSubring c))
      ∈ differentIdeal v.toValuationSubring (integralClosureAt F' v) :=
    aeval_derivative_mem_differentIdeal (A := v.toValuationSubring) (K := F) (L := F')
      (B := integralClosureAt F' v) c hadjF
  have himg : aeval (algebraMap (integralClosureAt F' v) F' c)
        (derivative (minpoly F (algebraMap (integralClosureAt F' v) F' c)))
      = algebraMap (integralClosureAt F' v) F'
          (aeval c (derivative (minpoly v.toValuationSubring c))) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions F F' hAc, derivative_map,
      aeval_map_algebraMap, aeval_algebraMap_apply]
  have hg0 : aeval (algebraMap (integralClosureAt F' v) F' c)
      (derivative (minpoly F (algebraMap (integralClosureAt F' v) F' c))) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable F _).aeval_derivative_ne_zero (minpoly.aeval F _)
  have hc0 : aeval c (derivative (minpoly v.toValuationSubring c)) ≠ 0 := by
    intro h; exact hg0 (by rw [himg, h, _root_.map_zero])
  have : FaithfulSMul v.toValuationSubring (integralClosureAt F' v) :=
    (faithfulSMul_iff_algebraMap_injective v.toValuationSubring (integralClosureAt F' v)).mpr
      (algebraMap_integralClosureAt_injective v)
  let : Algebra (FractionRing v.toValuationSubring) (FractionRing (integralClosureAt F' v)) :=
    FractionRing.liftAlgebra v.toValuationSubring (FractionRing (integralClosureAt F' v))
  have : IsScalarTower v.toValuationSubring (FractionRing v.toValuationSubring)
      (FractionRing (integralClosureAt F' v)) :=
    FractionRing.isScalarTower_liftAlgebra (R := v.toValuationSubring)
      (K := FractionRing (integralClosureAt F' v))
  have : Algebra.IsSeparable (FractionRing v.toValuationSubring)
      (FractionRing (integralClosureAt F' v)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv v.toValuationSubring F).symm.toRingEquiv
      (FractionRing.algEquiv (integralClosureAt F' v) F').symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv v.toValuationSubring F).symm
      (FractionRing.algEquiv (integralClosureAt F' v) F').symm _
  have := (fiberCenter F' v hw).isPrime
  have hdvd : (fiberCenter F' v hw).asIdeal
      ∣ differentIdeal v.toValuationSubring (integralClosureAt F' v) := by
    by_contra hnd
    have : Algebra.IsUnramifiedAt v.toValuationSubring (fiberCenter F' v hw).asIdeal :=
      not_dvd_differentIdeal_iff.mp hnd
    have he1 : Ideal.ramificationIdx'
        ((fiberCenter F' v hw).asIdeal.under v.toValuationSubring)
        (fiberCenter F' v hw).asIdeal = 1 :=
      (Ideal.ramificationIdx'_eq_ramificationIdx _ _
          (Ideal.under_ne_bot (A := v.toValuationSubring) (fiberCenter F' v hw).ne_bot)).trans
        Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    exact hram <| by
      rw [ramificationIndex_eq_ramificationIdx_fiberCenter hw,
        (fiberCenter_liesOver hw).over, he1]
  have hmem2 : aeval c (derivative (minpoly v.toValuationSubring c))
      ∈ (fiberCenter F' v hw).asIdeal := Ideal.le_of_dvd hdvd hmem
  rw [himg]
  exact (mem_fiberCenter_iff_ord_pos hw hc0).mp hmem2

end Place
end AlgebraicCurve
end

section

section

open WithZero

namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place

attribute [local instance 0] valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  have hkey := sum_ramificationIdx'_mul_inertiaDeg'_integralClosureAt (F' := F') v
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v ((hs w).mp hw)).asIdeal) ?_ ?_ ?_ ?_
  · intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v ((hs w).mp hw)).isPrime,
      fiberCenter_liesOver ((hs w).mp hw)⟩
  · intro w hw w' hw' h
    exact eq_of_fiberCenter_eq ((hs w).mp hw) ((hs w').mp hw')
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
      (hs _).mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  · intro w hw
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter ((hs w).mp hw),
      inertiaDeg_eq_inertiaDeg_fiberCenter ((hs w).mp hw)]

theorem sum_ramificationIndex_mul_deg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by
  have hsum := sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff v s hs
  calc ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = ∑ w ∈ s, (v.deg : ℤ) * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hdeg : (w.restrict F).deg * w.inertiaDeg F = w.deg :=
          deg_restrict_mul_inertiaDeg (K := K) (F := F) (w := w)
        rw [(hs w).mp hw] at hdeg
        rw [← hdeg]
        push_cast
        ring
    _ = (v.deg : ℤ) * ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
        rw [Finset.mul_sum]
    _ = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by rw [hsum]; ring

end Place

theorem ramificationInertiaIdentity_of_finiteDimensional
    (K F F' : Type*) [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] :
    RamificationInertiaIdentity K F F' := fun v s hs =>
  Place.sum_ramificationIndex_mul_deg_of_forall_mem_iff v s hs

end AlgebraicCurve
end

section

open scoped Polynomial

open WithZero
namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place

attribute [local instance 0] Place.valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section Structural

variable (v : Place K F)

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
theorem not_isField_integralClosureAt : ¬IsField (integralClosureAt F' v) := by
  intro hf
  exact ValuationSubring.not_isField_of_ne_top F v.ne_top'
    ((Algebra.IsIntegral.isField_iff_isField
      (R := v.toValuationSubring) (S := integralClosureAt F' v)
      (algebraMap_integralClosureAt_injective v)).mpr hf)

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
theorem ne_bot_of_isMaximal (P : Ideal (integralClosureAt F' v)) [hP : P.IsMaximal] :
    P ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField hP (not_isField_integralClosureAt v)

variable (F') in
def heightOneSpectrumOfIsMaximal (P : Ideal (integralClosureAt F' v)) [hP : P.IsMaximal] :
    HeightOneSpectrum (integralClosureAt F' v) :=
  ⟨P, hP.isPrime, ne_bot_of_isMaximal v P⟩

end Structural
end Place
end AlgebraicCurve

end

section

open WeierstrassCurve.Affine.Point

open scoped WeierstrassCurve.Affine

section

namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

@[scoped simp]
private theorem evalAt_zero : v.evalAt (0 : F) = 0 := by
  rw [← (algebraMap K F).map_zero, v.evalAt_algebraMap]

end Place
end AlgebraicCurve

end
end

section

open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine
open WeierstrassCurve.Affine.CoordinateRing
open WeierstrassCurve.Affine.CoordinateRing
variable {F : Type*} [Field F] (W : Affine F)

variable {W}

section OrdAtPoint

variable [IsDedekindDomain W.CoordinateRing]

theorem ord_polyToFunctionField_eq_zero_iff {x y : F} (h : W.Equation x y) {p : F[X]}
    (hp : p ≠ 0) :
    (placeOfEquation h).ord (polyToFunctionField W p) = 0 ↔ p.eval x ≠ 0 := by
  have h1 := ord_polyToFunctionField_pos_iff h hp (y := y)
  have h2 : 0 ≤ (placeOfEquation h).ord (polyToFunctionField W p) := by
    rw [polyToFunctionField_apply]
    exact ord_placeOfEquation_nonneg h _
  constructor
  · intro h0 hcon
    have h3 := h1.mpr hcon
    omega
  · intro hne
    rcases lt_or_eq_of_le h2 with hlt | heq
    · exact absurd (h1.mp hlt) hne
    · exact heq.symm

end OrdAtPoint
end Affine
end WeierstrassCurve

end

section

open WithZero

open scoped Polynomial.Bivariate

namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]
variable [Algebra K R] [Algebra K L] [IsScalarTower K R L]

theorem ord_ofHeightOneSpectrum_algebraMap_eq_one (w : HeightOneSpectrum R) {r : R}
    (hr : r ∈ w.asIdeal) (hr2 : r ∉ w.asIdeal ^ 2) :
    (ofHeightOneSpectrum (K := K) (F := L) w).ord (algebraMap R L r) = 1 := by
  have hr0 : r ≠ 0 := fun h => hr2 (h ▸ Submodule.zero_mem _)
  have hrL : algebraMap R L r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hr0
  rw [ord_ofHeightOneSpectrum_eq_neg_log w hrL, w.valuation_of_algebraMap]
  have h1 : w.intValuation r ≤ exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    simpa using hr
  have h2 : ¬ w.intValuation r ≤ exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact hr2
  rw [w.intValuation_if_neg hr0] at h1 h2 ⊢
  rw [exp_le_exp] at h1 h2
  rw [log_exp]
  omega

end Place
end AlgebraicCurve

namespace WeierstrassCurve
namespace Affine
variable {F : Type*} [Field F] {W : Affine F}

namespace CoordinateRing
open WeierstrassCurve.Affine.CoordinateRing

theorem derivative_polynomial : derivative W.polynomial = W.polynomialY := by
  rw [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.polynomialY,
    derivative_sub, derivative_add, derivative_sq, derivative_X, derivative_C_mul_X,
    derivative_C]
  simp only [mul_one, sub_zero, map_ofNat]

theorem evalEval_eq_zero_of_mem_span {x₀ y₀ : F} {z : F[X][Y]}
    (hz : z ∈ Ideal.span {C (X - C x₀), Y - C (C y₀)}) : z.evalEval x₀ y₀ = 0 :=
  mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mp hz

theorem evalEval_derivative_eq_zero_of_mem_span_sq {x₀ y₀ : F} {z : F[X][Y]}
    (hz : z ∈ Ideal.span {C (X - C x₀), Y - C (C y₀)} ^ 2) :
    (derivative z).evalEval x₀ y₀ = 0 := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun f hf g hg => ?_) (fun a b ha hb => ?_)
  · have hf0 : f.evalEval x₀ y₀ = 0 := evalEval_eq_zero_of_mem_span hf
    have hg0 : g.evalEval x₀ y₀ = 0 := evalEval_eq_zero_of_mem_span hg
    rw [derivative_mul, evalEval_add, evalEval_mul, evalEval_mul, hf0, hg0, mul_zero,
      zero_mul, add_zero]
  · rw [derivative_add, evalEval_add, ha, hb, add_zero]

theorem exists_eq_add_mul_polynomial_of_mem_XYIdeal_sq {x₀ y₀ : F} {r : F[X][Y]}
    (hr : mk W r ∈ XYIdeal W x₀ (C y₀) ^ 2) :
    ∃ z ∈ Ideal.span {C (X - C x₀), Y - C (C y₀)} ^ 2, ∃ δ : F[X][Y],
      r = z + δ * W.polynomial := by
  have hmap : XYIdeal W x₀ (C y₀)
      = Ideal.map (mk W) (Ideal.span {C (X - C x₀), Y - C (C y₀)}) := by
    rw [Ideal.map_span, Set.image_pair]
    rfl
  rw [hmap, ← Ideal.map_pow] at hr
  obtain ⟨z, hz, hzr⟩ := (Ideal.mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective).mp hr
  obtain ⟨δ, hδ⟩ := AdjoinRoot.mk_eq_mk.mp hzr
  exact ⟨z, hz, -δ, by linear_combination -hδ⟩

theorem X_sub_C_dvd_eval_of_mem_span {x₀ y₀ : F} {z : F[X][Y]}
    (hz : z ∈ Ideal.span {C (X - C x₀), Y - C (C y₀)}) :
    (X - C x₀ : F[X]) ∣ z.eval (C y₀) := by
  refine dvd_iff_isRoot.mpr ?_
  exact evalEval_eq_zero_of_mem_span hz

theorem X_sub_C_sq_dvd_eval_of_mem_span_sq {x₀ y₀ : F} {z : F[X][Y]}
    (hz : z ∈ Ideal.span {C (X - C x₀), Y - C (C y₀)} ^ 2) :
    (X - C x₀ : F[X]) ^ 2 ∣ z.eval (C y₀) := by
  rw [pow_two] at hz ⊢
  refine Submodule.mul_induction_on hz (fun f hf g hg => ?_) (fun a b ha hb => ?_)
  · rw [eval_mul]
    exact mul_dvd_mul (X_sub_C_dvd_eval_of_mem_span hf) (X_sub_C_dvd_eval_of_mem_span hg)
  · rw [eval_add]
    exact dvd_add ha hb

theorem XClass_notMem_XYIdeal_sq {x₀ y₀ : F} (heq : W.Equation x₀ y₀)
    (hY : W.polynomialY.evalEval x₀ y₀ ≠ 0) :
    XClass W x₀ ∉ XYIdeal W x₀ (C y₀) ^ 2 := by
  intro hmem
  have heq' : W.polynomial.evalEval x₀ y₀ = 0 := heq
  obtain ⟨z, hz, δ, hδ⟩ :=
    exists_eq_add_mul_polynomial_of_mem_XYIdeal_sq (r := C (X - C x₀)) hmem
  have hδP : δ.evalEval x₀ y₀ = 0 := by
    have h3 := congrArg (fun p => (derivative p).evalEval x₀ y₀) hδ
    simp only [derivative_C, evalEval_zero, derivative_add, derivative_mul, evalEval_add,
      evalEval_mul, evalEval_derivative_eq_zero_of_mem_span_sq hz, derivative_polynomial, heq',
      mul_zero, zero_add] at h3
    exact (mul_eq_zero.mp h3.symm).resolve_right hY
  have h4 := congrArg (Polynomial.eval (C y₀ : F[X])) hδ
  rw [eval_C, eval_add, eval_mul] at h4
  have hdvd : (X - C x₀ : F[X]) ^ 2
      ∣ z.eval (C y₀) + δ.eval (C y₀) * W.polynomial.eval (C y₀) := by
    refine dvd_add (X_sub_C_sq_dvd_eval_of_mem_span_sq hz) ?_
    rw [pow_two]
    exact mul_dvd_mul (dvd_iff_isRoot.mpr hδP) (dvd_iff_isRoot.mpr heq')
  rw [← h4] at hdvd
  have := Polynomial.natDegree_le_of_dvd hdvd (X_sub_C_ne_zero x₀)
  rw [natDegree_pow, natDegree_X_sub_C] at this
  omega

theorem YClass_notMem_XYIdeal_sq {x₀ y₀ : F} (heq : W.Equation x₀ y₀)
    (hY : W.polynomialY.evalEval x₀ y₀ = 0) :
    YClass W (C y₀) ∉ XYIdeal W x₀ (C y₀) ^ 2 := by
  intro hmem
  have heq' : W.polynomial.evalEval x₀ y₀ = 0 := heq
  obtain ⟨z, hz, δ, hδ⟩ :=
    exists_eq_add_mul_polynomial_of_mem_XYIdeal_sq (r := Y - C (C y₀)) hmem
  have h3 := congrArg (fun p => (derivative p).evalEval x₀ y₀) hδ
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, evalEval_one, derivative_add,
    derivative_mul, evalEval_add, evalEval_mul, evalEval_derivative_eq_zero_of_mem_span_sq hz,
    derivative_polynomial, heq', hY, mul_zero, add_zero] at h3
  exact one_ne_zero h3

end CoordinateRing

open WeierstrassCurve.Affine.CoordinateRing
open WeierstrassCurve.Affine.CoordinateRing

variable [IsDedekindDomain W.CoordinateRing]

theorem ord_placeOfEquation_XClass_self {x₀ y₀ : F} (heq : W.Equation x₀ y₀)
    (hY : W.polynomialY.evalEval x₀ y₀ ≠ 0) :
    (placeOfEquation heq).ord
      (algebraMap W.CoordinateRing W.FunctionField (XClass W x₀)) = 1 :=
  AlgebraicCurve.Place.ord_ofHeightOneSpectrum_algebraMap_eq_one
    (heightOneSpectrumOfEquation heq) (Ideal.subset_span (Set.mem_insert _ _))
    (XClass_notMem_XYIdeal_sq heq hY)

theorem ord_placeOfEquation_YClass_self {x₀ y₀ : F} (heq : W.Equation x₀ y₀)
    (hY : W.polynomialY.evalEval x₀ y₀ = 0) :
    (placeOfEquation heq).ord
      (algebraMap W.CoordinateRing W.FunctionField (YClass W (C y₀))) = 1 :=
  AlgebraicCurve.Place.ord_ofHeightOneSpectrum_algebraMap_eq_one
    (heightOneSpectrumOfEquation heq) (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    (YClass_notMem_XYIdeal_sq heq hY)

end Affine
end WeierstrassCurve

end

section

namespace AlgebraicCurve
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem fundamentalIdentityAlong_of_charZero [CharZero F] [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) :
    FundamentalIdentityAlong K φ hφ := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have : Module.Finite F F' := hfin
  have : Algebra.IsSeparable F F' := inferInstance
  have := isIntegral_along φ hφ
  exact (fundamentalIdentity_iff_ramificationInertiaIdentity).mpr
    (ramificationInertiaIdentity_of_finiteDimensional K F F')

end AlgebraicCurve
end

section

open IntermediateField

namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place

attribute [local instance 0] valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem exists_restrict_eq_of_separable (v : Place K F) :
    ∃ w : Place K F', w.restrict F = v := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (integralClosureAt F' v)
  have := hM
  exact ⟨placeOfPrime (heightOneSpectrumOfIsMaximal F' v M),
    restrict_placeOfPrime (heightOneSpectrumOfIsMaximal F' v M)⟩

end Place
end AlgebraicCurve
end

section

section

namespace ModularCurve
namespace Es1a1

section FiSupply

universe u

variable {F : Type u} [Field F] [CharZero F] {V W : Affine F}

theorem es1a3_fi_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι) :
    FundamentalIdentityAlong F ι hι :=
  haveI : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  fundamentalIdentityAlong_of_charZero ι hι hfin

end FiSupply

section FiDatum

universe u

variable {F : Type u} [Field F] [CharZero F] {W : Affine F}

theorem es1a3_fi_isogenyEndDatum (D : IsogenyEndDatum W) :
    FundamentalIdentityAlong F D.ι D.hι :=
  es1a3_fi_of_elliptic D.ι D.hι D.hfin

end FiDatum
end Es1a1
end ModularCurve
end
end

section

open WeierstrassCurve.Affine.Point

open scoped WeierstrassCurve.Affine

namespace AlgebraicCurve
namespace Place
open AlgebraicCurve.Place

theorem exists_restrictAlong_eq_of_finiteAlong
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [CharZero F]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (v : Place K F) : ∃ w : Place K F', w.restrictAlong φ hφ = v := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have : Module.Finite F F' := hfin
  have : Algebra.IsSeparable F F' := inferInstance
  obtain ⟨w, hw⟩ := Place.exists_restrict_eq_of_separable (K := K) (F' := F') v
  exact ⟨w, hw⟩

end Place
end AlgebraicCurve

end

section

section

open scoped Polynomial.Bivariate

namespace ModularCurve
namespace Es1a1

universe u

section FiSupply

variable {F : Type u} [Field F] [CharZero F] {V W : WeierstrassCurve.Affine F}

theorem es1a6_twFi_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι) :
    FundamentalIdentityAlong F ι hι :=
  haveI : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  fundamentalIdentityAlong_of_charZero ι hι hfin

end FiSupply
end Es1a1
end ModularCurve
end
end

section

section

open Function

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

omit [DecidableEq F] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_geomMorph_surjective (D : IsogenyEndDatum W) :
    Surjective D.geomMorph := fun Q => by
  have : CharZero W.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F W.FunctionField).injective
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_restrictAlong_eq_of_finiteAlong
    D.ι D.hι D.hfin (placeOfPoint Q)
  exact ⟨(placeOfPointEquiv W).symm w, placeOfPoint_injective (by
    rw [← D.placeOfPoint_geomMorph, placeOfPoint_placeOfPointEquiv_symm, hw])⟩

omit [GenusOnePlaceGate.IsCentred W] in
theorem kw_pointEnd_surjective (D : IsogenyEndDatum W) :
    Surjective (D.pointEnd' : W.Point → W.Point) := fun R => by
  obtain ⟨P, hP⟩ := kw_geomMorph_surjective D (R + D.geomMorph 0)
  exact ⟨P, by rw [D.pointEnd_eq_geomMorph_sub_geomMorph_zero, hP, add_sub_cancel_right]⟩

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

open Function

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

def kw_pointEnd_fiber_equiv_ker (D : IsogenyEndDatum W) (R : W.Point) :
    {P : W.Point // D.pointEnd' P = R} ≃ (AddMonoidHom.ker D.pointEnd') :=
  let P₀ : W.Point := (kw_pointEnd_surjective D R).choose
  have hP₀ : D.pointEnd' P₀ = R := (kw_pointEnd_surjective D R).choose_spec
  { toFun := fun ⟨P, hP⟩ => ⟨P - P₀, by
      change D.pointEnd' (P - P₀) = 0
      rw [map_sub, hP, hP₀, sub_self]⟩
    invFun := fun ⟨K, hK⟩ => ⟨K + P₀, by
      show D.pointEnd' (K + P₀) = R
      have hK' : D.pointEnd' K = 0 := hK
      rw [map_add, hK', zero_add, hP₀]⟩
    left_inv := fun ⟨P, _⟩ => Subtype.ext (sub_add_cancel P P₀)
    right_inv := fun ⟨K, _⟩ => Subtype.ext (add_sub_cancel_right K P₀) }

def kw_restrictAlong_fiber_equiv_pointEnd_fiber (D : IsogenyEndDatum W)
    (v : AlgebraicCurve.Place F W.FunctionField) :
    {w : AlgebraicCurve.Place F W.FunctionField // w.restrictAlong D.ι D.hι = v}
      ≃ {P : W.Point //
          D.pointEnd' P = (placeOfPointEquiv W).symm v - D.geomMorph 0} where
  toFun := fun ⟨w, hw⟩ => ⟨(placeOfPointEquiv W).symm w, by
    rw [D.pointEnd_eq_geomMorph_sub_geomMorph_zero, sub_left_inj]
    exact placeOfPoint_injective (by
      rw [← D.placeOfPoint_geomMorph, placeOfPoint_placeOfPointEquiv_symm, hw,
        placeOfPoint_placeOfPointEquiv_symm])⟩
  invFun := fun ⟨P, hP⟩ => ⟨placeOfPoint P, by
    rw [D.placeOfPoint_geomMorph P, ← placeOfPoint_placeOfPointEquiv_symm W v]
    congr 1
    have h : D.geomMorph P - D.geomMorph 0
        = (placeOfPointEquiv W).symm v - D.geomMorph 0 :=
      (D.pointEnd_eq_geomMorph_sub_geomMorph_zero P).symm.trans hP
    exact sub_left_injective h⟩
  left_inv := fun ⟨w, _⟩ => Subtype.ext (placeOfPoint_placeOfPointEquiv_symm W w)
  right_inv := fun ⟨P, _⟩ => Subtype.ext (placeOfPointEquiv_symm_placeOfPoint W P)

omit [IsAlgClosed F] [GenusOnePlaceGate.IsCentred W] in
theorem kw_natCard_restrictAlong_fiber_eq_ker (D : IsogenyEndDatum W)
    (v : AlgebraicCurve.Place F W.FunctionField) :
    Nat.card {w : AlgebraicCurve.Place F W.FunctionField //
        w.restrictAlong D.ι D.hι = v}
      = Nat.card (AddMonoidHom.ker D.pointEnd') :=
  Nat.card_congr ((kw_restrictAlong_fiber_equiv_pointEnd_fiber D v).trans
    (kw_pointEnd_fiber_equiv_ker D _))

def kw_ExistsUnramifiedBasePlace (D : IsogenyEndDatum W) : Prop :=
  letI := algebraAlong D.ι
  haveI := isScalarTower_along D.ι
  haveI := isIntegral_along D.ι D.hι
  ∃ v : AlgebraicCurve.Place F W.FunctionField,
    ∀ w : AlgebraicCurve.Place F W.FunctionField,
      w.restrict W.FunctionField = v → w.ramificationIndex W.FunctionField = 1

omit [DecidableEq F] [IsAlgClosed F] [WeierstrassCurve.IsElliptic W]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_natCard_restrictAlong_fiber_eq_degree_of_unramified (D : IsogenyEndDatum W)
    (v : AlgebraicCurve.Place F W.FunctionField)
    (hv : letI := algebraAlong D.ι
      haveI := isScalarTower_along D.ι
      haveI := isIntegral_along D.ι D.hι
      ∀ w : AlgebraicCurve.Place F W.FunctionField,
        w.restrict W.FunctionField = v → w.ramificationIndex W.FunctionField = 1) :
    Nat.card {w : AlgebraicCurve.Place F W.FunctionField //
        w.restrictAlong D.ι D.hι = v}
      = D.degree := by
  let := algebraAlong D.ι
  have := isScalarTower_along D.ι
  have := isIntegral_along D.ι D.hι
  have hFI' : FundamentalIdentity F W.FunctionField W.FunctionField :=
    ModularCurve.Es1a1.es1a6_twFi_of_elliptic D.ι D.hι D.hfin
  have hsum := ModularCurve.Es1a1.es1a1_dual_sum_ramificationIndex (K := F)
    (F := W.FunctionField) (F' := W.FunctionField)
    (deg_eq_one (W := W)) (deg_eq_one (W := W)) v
  have hcoll : ∀ w ∈ v.fiber W.FunctionField,
      (w.ramificationIndex W.FunctionField : ℤ) = 1 := by
    intro w hw
    rw [hv w (Place.mem_fiber.mp hw), Nat.cast_one]
  rw [Finset.sum_congr rfl hcoll, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hcard : (v.fiber W.FunctionField).card = D.degree := by
    have h : ((v.fiber W.FunctionField).card : ℤ) = (D.degree : ℤ) := hsum
    exact_mod_cast h
  rw [← hcard]
  refine Nat.card_congr ?_ |>.trans (Nat.card_eq_finsetCard _)
  exact {
    toFun := fun ⟨w, hw⟩ => ⟨w, Place.mem_fiber.mpr hw⟩
    invFun := fun ⟨w, hw⟩ => ⟨w, Place.mem_fiber.mp hw⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

omit [IsAlgClosed F] in
theorem kw_datumKernelDegreeFace_of_existsUnramified
    (hunram : ∀ D : IsogenyEndDatum W, kw_ExistsUnramifiedBasePlace D) :
    ModularCurve.cmm10_deg_DatumKernelDegreeFace W := fun D => by
  obtain ⟨v, hv⟩ := hunram D
  rw [← kw_natCard_restrictAlong_fiber_eq_ker D v,
    kw_natCard_restrictAlong_fiber_eq_degree_of_unramified D v hv]

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

open scoped Polynomial.Bivariate

namespace ModularCurve
namespace Es1a1

universe u

section AddLawCoreCmp

variable {F : Type u} [Field F]

variable (W : WeierstrassCurve.Affine F)

theorem es1a8_add_equation_cmp (φ : W.FunctionField →ₐ[F] W.FunctionField) :
    (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (φ (polyToFunctionField W X)) (φ (yGen W)) := by
  have h := equation_map_polyToFunctionField_yGen (W := W)
  rw [equation_iff'] at h
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  have h2 := congrArg φ h
  simp only [map_add, map_sub, map_mul, map_pow, _root_.map_zero, AlgHom.commutes] at h2
  rw [equation_iff']
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  linear_combination h2

end AddLawCoreCmp

end Es1a1
end ModularCurve
end
end

namespace WeierstrassCurve
namespace Affine
theorem kw_point_infinite {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]
    [AbelTheorem W] :
    Infinite W.Point :=
  WeierstrassCurve.point_infinite (W := W)

end Affine
end WeierstrassCurve

section

section

open Function
namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

theorem kw_existsUnramifiedBasePlace_proved (D : IsogenyEndDatum W) :
    kw_ExistsUnramifiedBasePlace D := by
  classical
  let := algebraAlong D.ι
  have := isScalarTower_along D.ι
  have := isIntegral_along D.ι D.hι
  have hfin : @Module.Finite W.FunctionField W.FunctionField _ _
    (@Algebra.toModule _ _ _ _ (algebraAlong D.ι)) := D.hfin
  have hcz : CharZero W.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F W.FunctionField).injective
  have hsep : Algebra.IsSeparable W.FunctionField W.FunctionField := inferInstance
  have hpd : HasPrincipalDivisors F W.FunctionField := hasPrincipalDivisors_functionField _
  obtain ⟨θ, hgen⟩ := Field.exists_primitive_element W.FunctionField W.FunctionField
  have hpmon : (minpoly W.FunctionField θ).Monic :=
    minpoly.monic (_root_.IsIntegral.of_finite W.FunctionField θ)
  have hg0 : aeval θ (derivative (minpoly W.FunctionField θ)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable W.FunctionField θ).aeval_derivative_ne_zero
      (minpoly.aeval W.FunctionField θ)
  let S₁ : Set (AlgebraicCurve.Place F W.FunctionField) :=
    ⋃ i ∈ (minpoly W.FunctionField θ).support,
      {v | (minpoly W.FunctionField θ).coeff i ∉ v.toValuationSubring}
  let S₂ : Set (AlgebraicCurve.Place F W.FunctionField) :=
    {w | w.ord (aeval θ (derivative (minpoly W.FunctionField θ))) ≠ 0}
  have hS₁fin : S₁.Finite :=
    Set.Finite.biUnion (minpoly W.FunctionField θ).support.finite_toSet fun i _ =>
      finite_setOf_notMem_toValuationSubring (K := F) ((minpoly W.FunctionField θ).coeff i)
  have hS₂fin : S₂.Finite := finite_setOf_ord_ne_zero_of_hasPrincipalDivisors (K := F) hg0
  have hSfin : (S₁ ∪ (fun w => w.restrict W.FunctionField) '' S₂).Finite :=
    hS₁fin.union (hS₂fin.image _)
  have : Infinite (AlgebraicCurve.Place F W.FunctionField) :=
    (placeOfPointEquiv W).symm.infinite_iff.mpr kw_point_infinite
  obtain ⟨v, hv⟩ := hSfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hv
  obtain ⟨hvS₁, hvS₂⟩ := hv
  refine ⟨v, fun w hw => ?_⟩
  by_contra hram
  have hcoeff : ∀ i, (minpoly W.FunctionField θ).coeff i ∈ v.toValuationSubring := by
    intro i
    by_contra hni
    have hci : (minpoly W.FunctionField θ).coeff i ≠ 0 :=
      fun h => hni (h ▸ v.toValuationSubring.zero_mem)
    exact hvS₁ (Set.mem_biUnion (Finset.mem_coe.mpr (mem_support_iff.mpr hci)) hni)
  obtain ⟨Q, hQmap, -, hQmon⟩ :=
    lifts_and_degree_eq_and_monic (mem_lifts_of_integralAt (fun i => hcoeff i)) hpmon
  have hθint : @_root_.IsIntegral v.toValuationSubring W.FunctionField _ _
      (AlgebraicCurve.Place.valuationSubringAlgebra W.FunctionField v) θ := by
    refine ⟨Q, hQmon, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ← Polynomial.eval₂_map, hQmap]
    exact minpoly.aeval W.FunctionField θ
  have hpos := AlgebraicCurve.Place.ord_deriv_pos_of_ramificationIndex_ne_one
    (K := F) (F := W.FunctionField) (F' := W.FunctionField)
    (v := v) (w := w) hw θ hgen hθint hram
  exact hvS₂ ⟨w, hpos.ne', hw⟩

theorem kw_datumKernelDegreeFace_unconditional :
    ModularCurve.cmm10_deg_DatumKernelDegreeFace W :=
  kw_datumKernelDegreeFace_of_existsUnramified kw_existsUnramifiedBasePlace_proved

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

namespace WeierstrassCurve
namespace Affine
universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

namespace IsogenyEndDatum

omit [DecidableEq F] [IsAlgClosed F] [WeierstrassCurve.IsElliptic W]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_iucz_sum_ramificationIndex_eq_degree (D : IsogenyEndDatum W)
    (v : AlgebraicCurve.Place F W.FunctionField) :
    letI := algebraAlong D.ι
    haveI := isScalarTower_along D.ι
    haveI := isIntegral_along D.ι D.hι
    ∑ w ∈ v.fiber W.FunctionField,
        (w.ramificationIndex W.FunctionField : ℤ)
      = (D.degree : ℤ) := by
  have _pin := Classical.em True
  let := algebraAlong D.ι
  have := isScalarTower_along D.ι
  have := isIntegral_along D.ι D.hι
  have hFI' : FundamentalIdentity F W.FunctionField W.FunctionField :=
    ModularCurve.Es1a1.es1a6_twFi_of_elliptic D.ι D.hι D.hfin
  exact ModularCurve.Es1a1.es1a1_dual_sum_ramificationIndex (K := F)
    (F := W.FunctionField) (F' := W.FunctionField)
    (deg_eq_one (W := W)) (deg_eq_one (W := W)) v

omit [IsAlgClosed F] [GenusOnePlaceGate.IsCentred W] in
theorem kw_iucz_unramified_of_existsUnramifiedBasePlace (D : IsogenyEndDatum W)
    (heub : kw_ExistsUnramifiedBasePlace D) :
    kw_ipfd_unramified D := by
  have _pin := Classical.em True
  classical
  let := algebraAlong D.ι
  have := isScalarTower_along D.ι
  have := isIntegral_along D.ι D.hι
  obtain ⟨v₀, hv₀⟩ := heub
  have hkd : Nat.card (AddMonoidHom.ker D.pointEnd') = D.degree := by
    rw [← kw_natCard_restrictAlong_fiber_eq_ker D v₀]
    exact kw_natCard_restrictAlong_fiber_eq_degree_of_unramified D v₀ hv₀
  intro P
  set v := (placeOfPoint P).restrictAlong D.ι D.hι with hv
  have hmem : placeOfPoint P ∈ v.fiber W.FunctionField := Place.mem_fiber.mpr rfl
  have hsum := kw_iucz_sum_ramificationIndex_eq_degree D v
  have hcard : (v.fiber W.FunctionField).card = D.degree := by
    have h1 : Nat.card {w : AlgebraicCurve.Place F W.FunctionField //
          w.restrictAlong D.ι D.hι = v}
        = (v.fiber W.FunctionField).card := by
      refine (Nat.card_congr ?_).trans (Nat.card_eq_finsetCard _)
      exact {
        toFun := fun ⟨w, hw⟩ => ⟨w, Place.mem_fiber.mpr hw⟩
        invFun := fun ⟨w, hw⟩ => ⟨w, Place.mem_fiber.mp hw⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← h1, kw_natCard_restrictAlong_fiber_eq_ker D v, hkd]
  have hpos : ∀ w ∈ v.fiber W.FunctionField,
      (1 : ℤ) ≤ (w.ramificationIndex W.FunctionField : ℤ) := fun w _ => by
    exact_mod_cast (w.ramificationIndex_pos (F := W.FunctionField))
  have heq : ((placeOfPoint P).ramificationIndex W.FunctionField : ℤ) = 1 := by
    have hge : (((v.fiber W.FunctionField).erase (placeOfPoint P)).card : ℤ)
        ≤ ∑ w ∈ (v.fiber W.FunctionField).erase (placeOfPoint P),
            (w.ramificationIndex W.FunctionField : ℤ) := by
      calc (((v.fiber W.FunctionField).erase (placeOfPoint P)).card : ℤ)
          = ∑ _w ∈ (v.fiber W.FunctionField).erase (placeOfPoint P), (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum fun w hw =>
            hpos w (Finset.mem_of_mem_erase hw)
    have hsplit :
        ((placeOfPoint P).ramificationIndex W.FunctionField : ℤ)
          + ∑ w ∈ (v.fiber W.FunctionField).erase (placeOfPoint P),
              (w.ramificationIndex W.FunctionField : ℤ)
          = (D.degree : ℤ) :=
      (Finset.add_sum_erase (v.fiber W.FunctionField)
        (fun w => (w.ramificationIndex W.FunctionField : ℤ)) hmem).trans hsum
    have hrest : ((v.fiber W.FunctionField).erase (placeOfPoint P)).card + 1
        = D.degree := by
      rw [Finset.card_erase_add_one hmem, hcard]
    have hge1 := hpos _ hmem
    omega
  change Place.ramificationIndexAlong D.ι (placeOfPoint P) = 1
  exact_mod_cast heq

end IsogenyEndDatum
end Affine
end WeierstrassCurve
end
end

namespace WeierstrassCurve
theorem surjective_zsmul_of_ne_zero {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] {m : ℤ} (hm : m ≠ 0) :
    Function.Surjective (fun P : W.toAffine.Point => m • P) := fun P =>
  WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed W hm P

end WeierstrassCurve

section

section

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

def kw_dualPointEnd (D : IsogenyEndDatum W) : AddMonoid.End W.Point :=
  ModularCurve.Es1a1.es1a1_dualPointEnd D
    (ModularCurve.Es1a1.es1a3_fi_isogenyEndDatum D)

omit [GenusOnePlaceGate.IsCentred W] in
omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
theorem kw_pointEnd_mul_dualPointEnd (D : IsogenyEndDatum W) :
    D.pointEnd' * kw_dualPointEnd D = ((D.degree : ℤ) : AddMonoid.End W.Point) :=
  ModularCurve.Es1a1.es1a1_pointEnd_mul_dualPointEnd D
    (ModularCurve.Es1a1.es1a3_fi_isogenyEndDatum D)

theorem kw_pointEnd_mul_cancel (D : IsogenyEndDatum W) (ψ : AddMonoid.End W.Point)
    (hzero : D.pointEnd' * ψ = 0) : ψ = 0 := by
  have hkerF : Nat.card (AddMonoidHom.ker (D.pointEnd' : W.Point →+ W.Point)) = D.degree :=
    kw_datumKernelDegreeFace_unconditional D
  have hdpos : (0 : ℤ) < (D.degree : ℤ) :=
    Int.natCast_pos.mpr (ModularCurve.cmm10_deg_degree_pos D)
  refine DFunLike.ext _ _ fun P => ?_
  obtain ⟨Q, hQ⟩ := WeierstrassCurve.surjective_zsmul_of_ne_zero (W := W)
    (m := (D.degree : ℤ)) hdpos.ne' P
  have hker : D.pointEnd' (ψ Q) = 0 := DFunLike.congr_fun hzero Q
  have hkill : (D.degree : ℤ) • ψ Q = 0 := by
    have := ModularCurve.cmm14_dex_card_ker_zsmul_eq_zero
      (D.pointEnd' : W.Point →+ W.Point) hker
    rwa [hkerF] at this
  change ψ P = 0
  rw [← hQ, map_zsmul]
  exact hkill

theorem kw_dualPointEnd_unique (D : IsogenyEndDatum W) (ψ : AddMonoid.End W.Point)
    (hψ : D.pointEnd' * ψ = ((D.degree : ℤ) : AddMonoid.End W.Point)) :
    ψ = kw_dualPointEnd D := by
  have hzero : D.pointEnd' * (ψ - kw_dualPointEnd D) = 0 := by
    rw [mul_sub, hψ, kw_pointEnd_mul_dualPointEnd D, sub_self]
  exact sub_eq_zero.mp (kw_pointEnd_mul_cancel D _ hzero)

def KwDualTraceWitness (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]
    :
    Prop :=
  ∀ D : IsogenyEndDatum W, ∃ t : ℤ,
    D.pointEnd' + kw_dualPointEnd D = ((t : ℤ) : AddMonoid.End W.Point)

omit [IsAlgClosed F] in
theorem kw_dualInSubring_of_traceWitness (htw : KwDualTraceWitness W)
    (D : IsogenyEndDatum W) :
    kw_dualPointEnd D ∈ isogenyEndSubring W (fun D => D.normFormulaAlong_auto) := by
  obtain ⟨t, htr⟩ := htw D
  have hψ : kw_dualPointEnd D
      = ((t : ℤ) : AddMonoid.End W.Point) - D.pointEnd' :=
    eq_sub_of_add_eq' htr
  rw [hψ]
  exact sub_mem (intCast_mem _ t)
    (WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd_mem_isogenyEndSubring _ (fun D =>
    D.normFormulaAlong_auto) D)

end GeneralW
end Affine
end WeierstrassCurve
end
end

namespace WeierstrassCurve
namespace Affine
scoped instance kw_charZero_end_point {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  [CharZero F]
    {W : Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]
    [AbelTheorem W] :
    CharZero (AddMonoid.End W.Point) := by
  have key : ∀ n : ℕ, (n : AddMonoid.End W.Point) = 0 → n = 0 := by
    intro n hn
    by_contra hne
    have htors : ∀ P : W.Point, (n : ℤ) • P = 0 := fun P => by
      have h := DFunLike.congr_fun hn P
      rw [AddMonoid.End.natCast_apply] at h
      simpa [natCast_zsmul] using h
    have : Finite (Submodule.torsionBy ℤ W.Point (n : ℤ)) :=
      WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero F W n (by exact_mod_cast hne)
    have hsurj : Function.Surjective
        (fun P : Submodule.torsionBy ℤ W.Point (n : ℤ) => (P : W.Point)) := fun P =>
      ⟨⟨P, (Submodule.mem_torsionBy_iff _ _).mpr (htors P)⟩, rfl⟩
    have : Finite W.Point := Finite.of_surjective _ hsurj
    exact (WeierstrassCurve.point_infinite (W := W)).not_finite ‹_›
  refine ⟨fun a b hab => ?_⟩
  rcases le_total a b with h | h
  · have h0 : ((b - a : ℕ) : AddMonoid.End W.Point) = 0 := by
      rw [Nat.cast_sub h, hab, sub_self]
    have := key _ h0; omega
  · have h0 : ((a - b : ℕ) : AddMonoid.End W.Point) = 0 := by
      rw [Nat.cast_sub h, hab, sub_self]
    have := key _ h0; omega

end Affine
end WeierstrassCurve

section

section

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

def kw_dualEndData_of_traceWitness (htw : KwDualTraceWitness W)
    (D : IsogenyEndDatum W) : AddMonoid.End.DualEndData D.pointEnd' :=
  ModularCurve.Es1a1.es1a4_twDualEndData_of_add_of_mul
    D.pointEnd' (kw_dualPointEnd D) (htw D).choose (D.degree : ℤ)
    (htw D).choose_spec (kw_pointEnd_mul_dualPointEnd D)

omit [IsAlgClosed F] in
@[scoped simp] theorem kw_dualEndData_of_traceWitness_dual (htw : KwDualTraceWitness W)
    (D : IsogenyEndDatum W) :
    (kw_dualEndData_of_traceWitness htw D).dual = kw_dualPointEnd D := rfl

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

theorem kw_pointEnd_ne_zero (D : IsogenyEndDatum W) : D.pointEnd' ≠ 0 := by
  intro hzero
  have hker : Nat.card (AddMonoidHom.ker D.pointEnd') = D.degree :=
    kw_datumKernelDegreeFace_unconditional D
  have hall : AddMonoidHom.ker D.pointEnd' = ⊤ := by
    rw [hzero]; exact AddMonoidHom.ker_zero
  have : Infinite W.Point := kw_point_infinite
  rw [hall, Nat.card_congr (AddSubgroup.topEquiv (G := W.Point)).toEquiv,
    Nat.card_eq_zero_of_infinite] at hker
  exact (ModularCurve.cmm10_deg_degree_pos D).ne' hker.symm

theorem kw_degree_eq_of_pointEnd_eq {D₁ D₂ : IsogenyEndDatum W}
    (h : D₁.pointEnd' = D₂.pointEnd') : D₁.degree = D₂.degree := by
  rw [← kw_datumKernelDegreeFace_unconditional D₁,
    ← kw_datumKernelDegreeFace_unconditional D₂, h]

theorem kw_dualPointEnd_eq_of_pointEnd_eq {D₁ D₂ : IsogenyEndDatum W}
    (h : D₁.pointEnd' = D₂.pointEnd') :
    kw_dualPointEnd D₁ = kw_dualPointEnd D₂ := by
  refine kw_dualPointEnd_unique D₂ _ ?_
  rw [← h, ← kw_degree_eq_of_pointEnd_eq h]
  exact kw_pointEnd_mul_dualPointEnd D₁

theorem kw_dualPointEnd_idDatum :
    kw_dualPointEnd (IsogenyEndDatum.idDatum W) = 1 := by
  refine (kw_dualPointEnd_unique (IsogenyEndDatum.idDatum W) 1 ?_).symm
  rw [IsogenyEndDatum.idDatum_pointEnd, IsogenyEndDatum.degree_idDatum, mul_one,
    Nat.cast_one, Int.cast_one]

theorem kw_degree_of_pointEnd_intCast (D : IsogenyEndDatum W) (n : ℤ)
    (hn : D.pointEnd' = ((n : ℤ) : AddMonoid.End W.Point)) :
    (D.degree : ℤ) = n ^ 2 := by
  have hne : n ≠ 0 := fun hz => kw_pointEnd_ne_zero D (by rw [hn, hz, Int.cast_zero])
  have hna : 1 ≤ n.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
  have htors : ∀ (m : ℤ) (x : W.Point),
      x ∈ AddMonoidHom.ker ((m : ℤ) : AddMonoid.End W.Point)
        ↔ x ∈ Submodule.torsionBy ℤ W.Point m := fun m x =>
    AddMonoidHom.mem_ker.trans (Submodule.mem_torsionBy_iff m x).symm
  have hcard :
      Nat.card (AddMonoidHom.ker D.pointEnd')
        = Nat.card (AddMonoidHom.ker ((n.natAbs : ℤ) : AddMonoid.End W.Point)) := by
    refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans
      (Equiv.subtypeEquivRight fun x => (htors (n.natAbs : ℤ) x).symm))
    rw [hn]
    refine (htors n x).trans ?_
    rw [Submodule.mem_torsionBy_iff, Submodule.mem_torsionBy_iff, natCast_zsmul]
    rcases Int.natAbs_eq n with h | h
    · conv_lhs => rw [h, natCast_zsmul]
    · conv_lhs => rw [h, neg_zsmul, natCast_zsmul, neg_eq_zero]
  rw [← kw_datumKernelDegreeFace_unconditional D, hcard,
    ModularCurve.cmm5_dp_natCard_ker_natCast (W := W) n.natAbs hna, Nat.cast_pow,
    Int.natAbs_sq]

theorem kw_dualPointEnd_of_pointEnd_intCast (D : IsogenyEndDatum W) (n : ℤ)
    (hn : D.pointEnd' = ((n : ℤ) : AddMonoid.End W.Point)) :
    kw_dualPointEnd D = ((n : ℤ) : AddMonoid.End W.Point) := by
  refine (kw_dualPointEnd_unique D _ ?_).symm
  rw [hn, ← Int.cast_mul, ← sq, ← kw_degree_of_pointEnd_intCast D n hn, Int.cast_natCast]

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

def KwShiftDatumSupply (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]
    :
    Prop :=
  ∀ D : IsogenyEndDatum W, 1 + D.pointEnd' ≠ 0 →
    ∃ D' : IsogenyEndDatum W,
      D'.pointEnd' = 1 + D.pointEnd' ∧
      kw_dualPointEnd D' = 1 + kw_dualPointEnd D

def KwDualConormAdditivityAtOne (W : Affine F) [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]
    :
    Prop :=
  ∀ D D' : IsogenyEndDatum W, D'.pointEnd' = 1 + D.pointEnd' →
    kw_dualPointEnd D' = 1 + kw_dualPointEnd D

omit [IsAlgClosed F] in
theorem kw_dualTraceWitness_of_shiftDatumSupply
    (hsh : KwShiftDatumSupply W) : KwDualTraceWitness W := by
  intro D
  have h := kw_pointEnd_mul_dualPointEnd D
  by_cases hzero : 1 + D.pointEnd' = 0
  · have hd : (1 + D.pointEnd') * kw_dualPointEnd D = 0 := by rw [hzero, zero_mul]
    have hd2 : kw_dualPointEnd D + D.pointEnd' * kw_dualPointEnd D = 0 := by
      rw [← hd, add_mul, one_mul]
    rw [h] at hd2
    have hψ : kw_dualPointEnd D
        = -(((D.degree : ℤ) : AddMonoid.End W.Point)) := by
      rw [← zero_sub, ← hd2]; abel
    have hφ : D.pointEnd' = 0 - 1 := by rw [← hzero]; abel
    refine ⟨-1 - (D.degree : ℤ), ?_⟩
    rw [Int.cast_sub, Int.cast_neg, Int.cast_one, hφ, hψ]
    abel
  · obtain ⟨D', hpt, hdual⟩ := hsh D hzero
    have h' := kw_pointEnd_mul_dualPointEnd D'
    rw [hpt, hdual] at h'
    have hexp : (1 + D.pointEnd') * (1 + kw_dualPointEnd D)
        = 1 + D.pointEnd' + (kw_dualPointEnd D
            + D.pointEnd' * kw_dualPointEnd D) := by
      rw [mul_add, mul_one, add_mul, one_mul]
    rw [hexp, h] at h'
    refine ⟨(D'.degree : ℤ) - (D.degree : ℤ) - 1, ?_⟩
    rw [Int.cast_sub, Int.cast_sub, Int.cast_one, ← h']
    abel

omit [IsAlgClosed F] in
theorem kw_shiftDatumSupply_of_addDatumSupply_of_dualAdditivity
    (hadd : ModularCurve.KwIsogenyEndAddDatumSupply W)
    (hdual : KwDualConormAdditivityAtOne W) :
    KwShiftDatumSupply W := by
  intro D hne
  have hne' : (IsogenyEndDatum.idDatum W).pointEnd' + D.pointEnd' ≠ 0 := by
    rwa [IsogenyEndDatum.idDatum_pointEnd]
  obtain ⟨D', hD'⟩ := hadd (IsogenyEndDatum.idDatum W) D hne'
  rw [IsogenyEndDatum.idDatum_pointEnd] at hD'
  exact ⟨D', hD', hdual D D' hD'⟩

omit [IsAlgClosed F] in
theorem kw_dualTraceWitness_of_addDatumSupply_of_dualAdditivity
    (hadd : ModularCurve.KwIsogenyEndAddDatumSupply W)
    (hdual : KwDualConormAdditivityAtOne W) :
    KwDualTraceWitness W :=
  kw_dualTraceWitness_of_shiftDatumSupply
    (kw_shiftDatumSupply_of_addDatumSupply_of_dualAdditivity hadd hdual)

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

namespace ModularCurve

namespace Es1a1

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

theorem kw_hk5f_dualTraceWitness_of_dualAdditivity
    (hdual : KwDualConormAdditivityAtOne W) :
    KwDualTraceWitness W :=
  kw_dualTraceWitness_of_addDatumSupply_of_dualAdditivity
    (kw_hk5f_addDatumSupply_proved W) hdual

end Es1a1
end ModularCurve
end
end

section

section

open ModularCurve.Es1a1

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

def KwDualAdditivityPhiRowGenericW : Prop :=
  ∀ D₁ D₂ D₃ : IsogenyEndDatum W, D₃.pointEnd' = D₁.pointEnd' + D₂.pointEnd' →
    kw_dualPointEnd D₃ = kw_dualPointEnd D₁ + kw_dualPointEnd D₂

def KwDCAOGeomMorphDualAdditivity : Prop :=
  ∀ D₁ D₂ D₃ : IsogenyEndDatum W,
    (∀ P : W.Point, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P) →
    kw_dualPointEnd D₃ = kw_dualPointEnd D₁ + kw_dualPointEnd D₂

variable {W}

theorem kw_dcao_of_phiRowGenericW (h : KwDualAdditivityPhiRowGenericW W) :
    KwDualConormAdditivityAtOne W := by
  intro D D' hpt
  have hpe : D'.pointEnd' = (IsogenyEndDatum.idDatum W).pointEnd' + D.pointEnd' := by
    rw [IsogenyEndDatum.idDatum_pointEnd]; exact hpt
  have hd := h (IsogenyEndDatum.idDatum W) D D' hpe
  rwa [kw_dualPointEnd_idDatum] at hd

omit [IsAlgClosed F] [GenusOnePlaceGate.IsCentred W] in
theorem kw_dcao_pointEnd_add_of_geomMorph_add {D₁ D₂ D₃ : IsogenyEndDatum W}
    (hgm : ∀ P : W.Point, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P) :
    D₃.pointEnd' = D₁.pointEnd' + D₂.pointEnd' := by
  refine DFunLike.ext _ _ fun P => ?_
  change D₃.pointEnd' P = D₁.pointEnd' P + D₂.pointEnd' P
  rw [D₁.pointEnd_eq_geomMorph_sub_geomMorph_zero,
    D₂.pointEnd_eq_geomMorph_sub_geomMorph_zero,
    D₃.pointEnd_eq_geomMorph_sub_geomMorph_zero, hgm P, hgm 0]
  abel

theorem kw_dcao_phiRowGenericW_of_geomMorphDualAdditivity
    (h : KwDCAOGeomMorphDualAdditivity W) :
    KwDualAdditivityPhiRowGenericW W := by
  intro D₁ D₂ D₃ hpe
  have hne : D₁.pointEnd' + D₂.pointEnd' ≠ 0 := hpe ▸ kw_pointEnd_ne_zero D₃
  obtain ⟨D₃', hgm⟩ := kw_hk5f_addGeomMorphSupply_proved W D₁ D₂ hne
  have hpe' : D₃'.pointEnd' = D₃.pointEnd' :=
    (kw_dcao_pointEnd_add_of_geomMorph_add hgm).trans hpe.symm
  rw [kw_dualPointEnd_eq_of_pointEnd_eq hpe'.symm]
  exact h D₁ D₂ D₃' hgm

theorem kw_dcao_of_geomMorphDualAdditivity
    (h : KwDCAOGeomMorphDualAdditivity W) :
    KwDualConormAdditivityAtOne W :=
  kw_dcao_of_phiRowGenericW (kw_dcao_phiRowGenericW_of_geomMorphDualAdditivity h)

theorem kw_dcao_htw_of_geomMorphDualAdditivity
    (h : KwDCAOGeomMorphDualAdditivity W) :
    KwDualTraceWitness W :=
  kw_hk5f_dualTraceWitness_of_dualAdditivity W (kw_dcao_of_geomMorphDualAdditivity h)

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

open ModularCurve.Es1a1
namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

local instance kw_dcao_instHPD : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField _

theorem kw_dcao_unramified_proved (D : IsogenyEndDatum W) :
    IsogenyEndDatum.kw_ipfd_unramified D :=
  IsogenyEndDatum.kw_iucz_unramified_of_existsUnramifiedBasePlace D
    (kw_existsUnramifiedBasePlace_proved D)

omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] [GenusOnePlaceGate.IsCentred W] in
theorem kw_dcao_divisorSum_pullbackAlong (D : IsogenyEndDatum W)
    (E : AlgebraicCurve.Divisor F W.FunctionField) (hE : Divisor.degree E = 0) :
    divisorSum (Divisor.pullbackAlong D.ι D.hι E)
      = kw_dualPointEnd D (divisorSum E) := by
  have hsymm : (genusOnePic0Equiv W).symm (divisorSum E)
      = Pic0.mk ⟨E, Divisor.mem_degZero.mpr hE⟩ := by
    apply (genusOnePic0Equiv W).injective
    rw [AddEquiv.apply_symm_apply, genusOnePic0Equiv_apply, pic0ToPoint_mk]
  change _ = es1a1_dualPointEnd D (es1a3_fi_isogenyEndDatum D) (divisorSum E)
  rw [es1a1_dualPointEnd_apply, hsymm, es1a1_conormPic0Hom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, es1a1_coe_conormDegZero]

omit [DecidableEq F] [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] [W.GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_dcao_defect_degree_zero (D₁ D₂ D₃ : IsogenyEndDatum W)
    (E : AlgebraicCurve.Divisor F W.FunctionField) (hE : Divisor.degree E = 0) :
    Divisor.degree
      (Divisor.pullbackAlong D₃.ι D₃.hι E
        - (Divisor.pullbackAlong D₁.ι D₁.hι E + Divisor.pullbackAlong D₂.ι D₂.hι E))
      = 0 := by
  rw [map_sub, map_add,
    Divisor.degree_pullbackAlong D₃.ι D₃.hι (es1a3_fi_isogenyEndDatum D₃),
    Divisor.degree_pullbackAlong D₁.ι D₁.hι (es1a3_fi_isogenyEndDatum D₁),
    Divisor.degree_pullbackAlong D₂.ι D₂.hι (es1a3_fi_isogenyEndDatum D₂), hE]
  ring

omit [IsAlgClosed F] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_dcao_defect_pullback_placeOfPoint_apply_of_unramified
    (D₁ D₂ D₃ : IsogenyEndDatum W)
    (h1 : IsogenyEndDatum.kw_ipfd_unramified D₁)
    (h2 : IsogenyEndDatum.kw_ipfd_unramified D₂)
    (h3 : IsogenyEndDatum.kw_ipfd_unramified D₃)
    (Q P : W.Point) :
    (Divisor.pullbackAlong D₃.ι D₃.hι (Finsupp.single (placeOfPoint Q) 1)
        - Divisor.pullbackAlong D₁.ι D₁.hι (Finsupp.single (placeOfPoint Q) 1)
        - Divisor.pullbackAlong D₂.ι D₂.hι (Finsupp.single (placeOfPoint Q) 1))
      (placeOfPoint P)
      = (if D₃.geomMorph P = Q then 1 else 0)
        - (if D₁.geomMorph P = Q then 1 else 0)
        - (if D₂.geomMorph P = Q then 1 else 0) := by
  rw [Finsupp.sub_apply, Finsupp.sub_apply,
    IsogenyEndDatum.kw_ipfd_pullbackAlong_single_placeOfPoint_apply_of_unramified
      D₃ h3 Q P,
    IsogenyEndDatum.kw_ipfd_pullbackAlong_single_placeOfPoint_apply_of_unramified
      D₁ h1 Q P,
    IsogenyEndDatum.kw_ipfd_pullbackAlong_single_placeOfPoint_apply_of_unramified
      D₂ h2 Q P]

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_dcao_compDatum_degree (D₁ D₂ : IsogenyEndDatum W) :
    (IsogenyEndDatum.compDatum W D₁ D₂).degree = D₁.degree * D₂.degree := by
  change finrankAlong F (IsogenyEndDatum.compDatum W D₁ D₂).ι
    = finrankAlong F D₁.ι * finrankAlong F D₂.ι
  rw [IsogenyEndDatum.compDatum_ι, finrankAlong_comp]

theorem kw_dcao_dual_comp (D₁ D₂ : IsogenyEndDatum W) :
    kw_dualPointEnd (IsogenyEndDatum.compDatum W D₁ D₂)
      = kw_dualPointEnd D₂ * kw_dualPointEnd D₁ := by
  refine (kw_dualPointEnd_unique (IsogenyEndDatum.compDatum W D₁ D₂) _ ?_).symm
  rw [es1a3_compDatum_pointEnd,
    show (((IsogenyEndDatum.compDatum W D₁ D₂).degree : ℤ) : AddMonoid.End W.Point)
      = ((D₂.degree : ℤ) : AddMonoid.End W.Point)
          * ((D₁.degree : ℤ) : AddMonoid.End W.Point) by
      rw [kw_dcao_compDatum_degree, Nat.cast_mul, Int.cast_mul]
      exact Int.cast_comm _ _]
  calc D₁.pointEnd' * D₂.pointEnd' * (kw_dualPointEnd D₂ * kw_dualPointEnd D₁)
      = D₁.pointEnd' * (D₂.pointEnd' * kw_dualPointEnd D₂) * kw_dualPointEnd D₁ := by
        rw [mul_assoc, mul_assoc, mul_assoc]
    _ = D₁.pointEnd' * ((D₂.degree : ℤ) : AddMonoid.End W.Point)
          * kw_dualPointEnd D₁ := by rw [kw_pointEnd_mul_dualPointEnd D₂]
    _ = ((D₂.degree : ℤ) : AddMonoid.End W.Point)
          * (D₁.pointEnd' * kw_dualPointEnd D₁) := by
        rw [← Int.cast_comm, mul_assoc]
    _ = ((D₂.degree : ℤ) : AddMonoid.End W.Point)
          * ((D₁.degree : ℤ) : AddMonoid.End W.Point) := by
        rw [kw_pointEnd_mul_dualPointEnd D₁]

variable (W) in
def KwDCAODefectPrincipalPerPoint : Prop :=
  ∀ D₁ D₂ D₃ : IsogenyEndDatum W,
    (∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P) →
      D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X) →
        ∀ L : W.Point, Divisor.IsPrincipal
          (Divisor.pullbackAlong D₃.ι D₃.hι
              (pointDivisor L : AlgebraicCurve.Divisor F W.FunctionField)
            - (Divisor.pullbackAlong D₁.ι D₁.hι
                  (pointDivisor L : AlgebraicCurve.Divisor F W.FunctionField)
                + Divisor.pullbackAlong D₂.ι D₂.hι
                  (pointDivisor L : AlgebraicCurve.Divisor F W.FunctionField)))

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_dcao_ext_of_iota_eq {D₁ D₂ : IsogenyEndDatum W} (h : D₁.ι = D₂.ι) :
    D₁ = D₂ := by
  cases D₁; cases D₂
  simp only [IsogenyEndDatum.mk.injEq] at h ⊢
  exact h

theorem kw_dcao_geomMorphDualAdditivity_of_defectPrincipal
    (hdef : KwDCAODefectPrincipalPerPoint W) :
    KwDCAOGeomMorphDualAdditivity W := by
  intro D₁ D₂ D₃ hgm
  have hpe : D₃.pointEnd' = D₁.pointEnd' + D₂.pointEnd' :=
    kw_dcao_pointEnd_add_of_geomMorph_add hgm
  by_cases hX : D₁.ι (polyToFunctionField W X) = D₂.ι (polyToFunctionField W X)
  · have heq₁ := es1a8_add_equation_cmp W D₁.ι
    have heq₂ := es1a8_add_equation_cmp W D₂.ι
    by_cases hneg : D₁.ι (yGen W)
        = (W.map (algebraMap F W.FunctionField)).toAffine.negY
            (D₂.ι (polyToFunctionField W X)) (D₂.ι (yGen W))
    · have hcol : es1a8_addCollapse_cmp W D₁.ι D₂.ι := ⟨hX, hneg⟩
      exact absurd (hpe.trans (es1a8_addCollapse_pointEnd_add_eq_zero_cmp D₁ D₂ hcol))
        (kw_pointEnd_ne_zero D₃)
    · have hY : D₁.ι (yGen W) = D₂.ι (yGen W) := Y_eq_of_Y_ne heq₁ heq₂ hX hneg
      have hDeq : D₁ = D₂ :=
        kw_dcao_ext_of_iota_eq (es1a8_functionField_algHom_ext_cmp hX hY)
      subst hDeq
      have h2cast : ((2 : ℤ) : AddMonoid.End W.Point) = 1 + 1 := by norm_num
      have h2ne : (IsogenyEndDatum.idDatum W).pointEnd'
          + (IsogenyEndDatum.idDatum W).pointEnd' ≠ 0 := by
        rw [IsogenyEndDatum.idDatum_pointEnd, one_add_one_eq_two]
        have := kw_charZero_end_point (W := W)
        exact two_ne_zero
      obtain ⟨DN, hDNgm⟩ := kw_hk5f_addGeomMorphSupply_proved W
        (IsogenyEndDatum.idDatum W) (IsogenyEndDatum.idDatum W) h2ne
      have hDN2 : DN.pointEnd' = ((2 : ℤ) : AddMonoid.End W.Point) := by
        have h := kw_dcao_pointEnd_add_of_geomMorph_add hDNgm
        rw [IsogenyEndDatum.idDatum_pointEnd] at h
        rw [h, h2cast]
      have hCpe : (IsogenyEndDatum.compDatum W DN D₁).pointEnd' = D₃.pointEnd' := by
        rw [es1a3_compDatum_pointEnd, hDN2, hpe, h2cast, add_mul, one_mul]
      rw [kw_dualPointEnd_eq_of_pointEnd_eq hCpe.symm, kw_dcao_dual_comp,
        kw_dualPointEnd_of_pointEnd_intCast DN 2 hDN2, h2cast, mul_add, mul_one]
  · refine DFunLike.ext _ _ fun Q => ?_
    change kw_dualPointEnd D₃ Q = kw_dualPointEnd D₁ Q + kw_dualPointEnd D₂ Q
    have hE : Divisor.degree
        (pointDivisor Q : AlgebraicCurve.Divisor F W.FunctionField) = 0 :=
      Divisor.mem_degZero.mp (pointDivisor Q).2
    have h0 : divisorSum
        (Divisor.pullbackAlong D₃.ι D₃.hι
            (pointDivisor Q : AlgebraicCurve.Divisor F W.FunctionField)
          - (Divisor.pullbackAlong D₁.ι D₁.hι
                (pointDivisor Q : AlgebraicCurve.Divisor F W.FunctionField)
              + Divisor.pullbackAlong D₂.ι D₂.hι
                (pointDivisor Q : AlgebraicCurve.Divisor F W.FunctionField))) = 0 :=
      divisorSum_eq_zero_of_isPrincipal
        (kw_dcao_defect_degree_zero D₁ D₂ D₃ _ hE) (hdef D₁ D₂ D₃ hgm hX Q)
    rw [map_sub, map_add, kw_dcao_divisorSum_pullbackAlong D₃ _ hE,
      kw_dcao_divisorSum_pullbackAlong D₁ _ hE,
      kw_dcao_divisorSum_pullbackAlong D₂ _ hE,
      divisorSum_pointDivisor, sub_eq_zero] at h0
    exact h0

theorem kw_dcao_htw_of_defectPrincipal (hdef : KwDCAODefectPrincipalPerPoint W) :
    KwDualTraceWitness W :=
  kw_dcao_htw_of_geomMorphDualAdditivity
    (kw_dcao_geomMorphDualAdditivity_of_defectPrincipal hdef)

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

open ModularCurve.Es1a1
open ModularCurve.Mmr73
namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

attribute [local instance] ModularCurve.Es1a1.instDecEqFunctionFieldEs1a6Add

abbrev kw_dcao_lineSlope (D₁ D₂ : IsogenyEndDatum W) : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).toAffine.slope
    (D₁.ι (polyToFunctionField W X)) (D₂.ι (polyToFunctionField W X))
    (D₁.ι (yGen W)) (D₂.ι (yGen W))

abbrev kw_dcao_lineIntercept (D₁ D₂ : IsogenyEndDatum W) : W.FunctionField :=
  D₁.ι (yGen W) - kw_dcao_lineSlope D₁ D₂ * D₁.ι (polyToFunctionField W X)

abbrev kw_dcao_specVert (D₁ D₂ : IsogenyEndDatum W) (a : F) : W.FunctionField :=
  algebraMap F W.FunctionField a - es1a6_addSumX W D₁.ι D₂.ι

abbrev kw_dcao_specLine (D₁ D₂ : IsogenyEndDatum W) (a b : F) : W.FunctionField :=
  algebraMap F W.FunctionField b
    - kw_dcao_lineSlope D₁ D₂ * algebraMap F W.FunctionField a
    - kw_dcao_lineIntercept D₁ D₂

theorem kw_dcao_addSumX_nonconst_of_hgm (D₁ D₂ D₃ : IsogenyEndDatum W)
    (hgm : ∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P) (c : F) :
    es1a6_addSumX W D₁.ι D₂.ι ≠ algebraMap F W.FunctionField c :=
  kw_hk5f_addSumXNonConstGuardAt_proved W D₁ D₂
    ((kw_dcao_pointEnd_add_of_geomMorph_add hgm) ▸ kw_pointEnd_ne_zero D₃) c

theorem kw_dcao_specVert_ne_zero_of_hgm (D₁ D₂ D₃ : IsogenyEndDatum W)
    (hgm : ∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P) (a : F) :
    kw_dcao_specVert D₁ D₂ a ≠ 0 :=
  fun hV => kw_dcao_addSumX_nonconst_of_hgm D₁ D₂ D₃ hgm a (sub_eq_zero.mp hV).symm

theorem kw_dcao_sumDatum_of_hgm (D₁ D₂ D₃ : IsogenyEndDatum W)
    (hgm : ∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P)
    (hX : D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X)) :
    ∃ Ds : IsogenyEndDatum W,
      Ds.ι (polyToFunctionField W X) = es1a6_addSumX W D₁.ι D₂.ι
      ∧ ∀ P, Ds.geomMorph P = D₁.geomMorph P + D₂.geomMorph P := by
  have hnc := kw_dcao_addSumX_nonconst_of_hgm D₁ D₂ D₃ hgm
  have hcol : ¬ es1a6_addCollapse W D₁.ι D₂.ι :=
    es1a6_add_not_collapse_of_X_ne W D₁.ι D₂.ι hX
  have htr : Function.Injective
      (Polynomial.aeval (R := F) (es1a6_addSumX W D₁.ι D₂.ι)) :=
    es1a6_add_aeval_sumX_injective_of_forall_ne W D₁.ι D₂.ι hnc
  obtain ⟨hι, hfin⟩ := kw_hk5f_addIntegralFiniteDataAt_proved W D₁ D₂ hcol htr
  refine ⟨⟨es1a6_addSumPullbackHom W D₁.ι D₂.ι hcol htr, hι, hfin⟩,
    es1a6_addSumPullbackHom_X W D₁.ι D₂.ι hcol htr, fun P => ?_⟩
  have h1 := kw_coordSeamDataAt_geomMorph D₁ P
  have h2 := kw_coordSeamDataAt_geomMorph D₂ P
  have hsum := kw_hk5f_addSumCoordSeamDataNCAt_proved W D₁.ι D₂.ι hcol hnc
    (placeOfPoint P) (D₁.geomMorph P) (D₂.geomMorph P) h1 h2
  have hseam := es1a6_addSumSeam_of_data D₁.ι D₂.ι hcol htr hι P
    (D₁.geomMorph P + D₂.geomMorph P) hsum
  exact placeOfPoint_injective
    (((⟨_, hι, hfin⟩ : IsogenyEndDatum W).placeOfPoint_geomMorph P).symm.trans hseam)

theorem kw_dcao_ord_Dtransport (D : IsogenyEndDatum W) (f : W.FunctionField)
    (P : W.Point) :
    (placeOfPoint P).ord (D.ι f) = (placeOfPoint (D.geomMorph P)).ord f := by
  rw [(placeOfPoint P).ord_restrictAlong D.ι D.hι,
    kw_dcao_unramified_proved D P, Nat.cast_one, one_mul,
    D.placeOfPoint_geomMorph P]

theorem kw_dcao_ord_specVert_eq_transport (D₁ D₂ D₃ : IsogenyEndDatum W)
    (hgm : ∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P)
    (hX : D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X))
    (a : F) (P : W.Point) :
    (placeOfPoint P).ord (kw_dcao_specVert D₁ D₂ a)
      = (placeOfPoint (D₁.geomMorph P + D₂.geomMorph P)).ord
          (algebraMap F W.FunctionField a - polyToFunctionField W X) := by
  obtain ⟨Ds, hXs, hgms⟩ := kw_dcao_sumDatum_of_hgm D₁ D₂ D₃ hgm hX
  have hsp : kw_dcao_specVert D₁ D₂ a
      = Ds.ι (algebraMap F W.FunctionField a - polyToFunctionField W X) := by
    change algebraMap F W.FunctionField a - es1a6_addSumX W D₁.ι D₂.ι = _
    rw [map_sub, Ds.ι.commutes, hXs]
  rw [hsp, kw_dcao_ord_Dtransport Ds, hgms P]

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_dcao_specLine_negY_product (D₁ D₂ : IsogenyEndDatum W)
    (hX : D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X))
    {a b : F} (h : W.Nonsingular a b) :
    kw_dcao_specLine D₁ D₂ a b
        * kw_dcao_specLine D₁ D₂ a (W.toAffine.negY a b)
      = -((algebraMap F W.FunctionField a - D₁.ι (polyToFunctionField W X))
          * (algebraMap F W.FunctionField a - D₂.ι (polyToFunctionField W X))
          * kw_dcao_specVert D₁ D₂ a) := by
  set x₁ := D₁.ι (polyToFunctionField W X) with hx₁
  set x₂ := D₂.ι (polyToFunctionField W X) with hx₂
  set y₁ := D₁.ι (yGen W) with hy₁
  set y₂ := D₂.ι (yGen W) with hy₂
  have hE₁ := es1a6_add_equation W D₁.ι
  have hE₂ := es1a6_add_equation W D₂.ι
  simp only [← hx₁, ← hx₂, ← hy₁, ← hy₂] at hE₁ hE₂
  have hxy : ¬(x₁ = x₂ ∧ y₁
      = (W.map (algebraMap F W.FunctionField)).toAffine.negY x₂ y₂) :=
    fun ⟨hx, _⟩ => hX hx
  have haps := addPolynomial_slope hE₁ hE₂ hxy
  have hcap := (W.map (algebraMap F W.FunctionField)).toAffine.C_addPolynomial
      x₁ y₁ (kw_dcao_lineSlope D₁ D₂)
  rw [show kw_dcao_lineSlope D₁ D₂
    = (W.map (algebraMap F W.FunctionField)).toAffine.slope x₁ x₂ y₁ y₂ from rfl,
    haps] at hcap
  have heval := congrArg
    (Polynomial.evalEval (algebraMap F W.FunctionField a)
      (algebraMap F W.FunctionField b)) hcap
  have hEab : (W.map (algebraMap F W.FunctionField)).toAffine.Equation
        (algebraMap F W.FunctionField a) (algebraMap F W.FunctionField b) := by
    have := h.1
    rw [Affine.equation_iff] at this ⊢
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    exact_mod_cast congrArg (algebraMap F W.FunctionField) this
  simp only [Polynomial.evalEval_C, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.evalEval_add, Polynomial.evalEval_mul, Polynomial.evalEval_sub,
    Affine.evalEval_negPolynomial,
    show (W.map (algebraMap F W.FunctionField)).toAffine.polynomial.evalEval
          (algebraMap F W.FunctionField a) (algebraMap F W.FunctionField b) = 0 from hEab,
    add_zero, linePolynomial, Polynomial.eval_add, Polynomial.evalEval_X] at heval
  have hsl : kw_dcao_lineSlope D₁ D₂
      = (W.map (algebraMap F W.FunctionField)).toAffine.slope x₁ x₂ y₁ y₂ := rfl
  have hint : kw_dcao_lineIntercept D₁ D₂ = y₁ - kw_dcao_lineSlope D₁ D₂ * x₁ := rfl
  have hnegY : (W.map (algebraMap F W.FunctionField)).toAffine.negY
          (algebraMap F W.FunctionField a) (algebraMap F W.FunctionField b)
      = algebraMap F W.FunctionField (W.toAffine.negY a b) := by
    simp only [Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_sub,
      _root_.map_neg, map_mul]
  change (_ - _ * _ - kw_dcao_lineIntercept D₁ D₂)
    * (_ - _ * _ - kw_dcao_lineIntercept D₁ D₂)
    = -((_ - x₁) * (_ - x₂) * (_ - es1a6_addSumX W D₁.ι D₂.ι))
  rw [hint, hsl, show es1a6_addSumX W D₁.ι D₂.ι
    = (W.map (algebraMap F W.FunctionField)).toAffine.addX x₁ x₂
        ((W.map (algebraMap F W.FunctionField)).toAffine.slope x₁ x₂ y₁ y₂) from rfl,
    ← hnegY]
  linear_combination heval.symm

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_dcao_algebraMap_sub_X_ne_zero (a : F) :
    algebraMap F W.FunctionField a - polyToFunctionField W X ≠ 0 := by
  rw [sub_ne_zero, ← polyToFunctionField_C]
  exact fun hc => X_ne_C a (polyToFunctionField_injective hc).symm

theorem kw_dcao_specLine_ne_zero_of_hgm (D₁ D₂ D₃ : IsogenyEndDatum W)
    (hgm : ∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P)
    (hX : D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X))
    {a b : F} (h : W.Nonsingular a b) :
    kw_dcao_specLine D₁ D₂ a b ≠ 0 := by
  intro hL
  have hprod := kw_dcao_specLine_negY_product D₁ D₂ hX h
  rw [hL, zero_mul, eq_comm, neg_eq_zero] at hprod
  have h1 : algebraMap F W.FunctionField a - D₁.ι (polyToFunctionField W X) ≠ 0 := by
    rw [show algebraMap F W.FunctionField a = D₁.ι (algebraMap F W.FunctionField a) from
        (D₁.ι.commutes a).symm, ← map_sub]
    exact mmr73_cs_iota_ne_zero D₁ (kw_dcao_algebraMap_sub_X_ne_zero a)
  have h2 : algebraMap F W.FunctionField a - D₂.ι (polyToFunctionField W X) ≠ 0 := by
    rw [show algebraMap F W.FunctionField a = D₂.ι (algebraMap F W.FunctionField a) from
        (D₂.ι.commutes a).symm, ← map_sub]
    exact mmr73_cs_iota_ne_zero D₂ (kw_dcao_algebraMap_sub_X_ne_zero a)
  exact (mul_ne_zero (mul_ne_zero h1 h2)
    (kw_dcao_specVert_ne_zero_of_hgm D₁ D₂ D₃ hgm a)) hprod

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_dcao_specLine_negY_diff (D₁ D₂ : IsogenyEndDatum W) (a b : F) :
    kw_dcao_specLine D₁ D₂ a b - kw_dcao_specLine D₁ D₂ a (W.toAffine.negY a b)
      = algebraMap F W.FunctionField (b - W.toAffine.negY a b) := by
  change (_ - _ - _) - (_ - _ - _) = _
  rw [map_sub]; ring

theorem kw_dcao_specLine_ord_sum (D₁ D₂ D₃ : IsogenyEndDatum W)
    (hgm : ∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P)
    (hX : D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X))
    {a b : F} (h : W.Nonsingular a b) (P : W.Point) :
    (placeOfPoint P).ord (kw_dcao_specLine D₁ D₂ a b)
        + (placeOfPoint P).ord (kw_dcao_specLine D₁ D₂ a (W.toAffine.negY a b))
      = (placeOfPoint (D₁.geomMorph P)).ord
            (algebraMap F W.FunctionField a - polyToFunctionField W X)
        + (placeOfPoint (D₂.geomMorph P)).ord
            (algebraMap F W.FunctionField a - polyToFunctionField W X)
        + (placeOfPoint (D₁.geomMorph P + D₂.geomMorph P)).ord
            (algebraMap F W.FunctionField a - polyToFunctionField W X) := by
  have hLne := kw_dcao_specLine_ne_zero_of_hgm D₁ D₂ D₃ hgm hX h
  have hL'ne' : kw_dcao_specLine D₁ D₂ a (W.toAffine.negY a b) ≠ 0 :=
    kw_dcao_specLine_ne_zero_of_hgm D₁ D₂ D₃ hgm hX ((Affine.nonsingular_neg a b).mpr h)
  have hprod := kw_dcao_specLine_negY_product D₁ D₂ hX h
  have h1 : algebraMap F W.FunctionField a - D₁.ι (polyToFunctionField W X)
      = D₁.ι (algebraMap F W.FunctionField a - polyToFunctionField W X) := by
    rw [map_sub, D₁.ι.commutes]
  have h2 : algebraMap F W.FunctionField a - D₂.ι (polyToFunctionField W X)
      = D₂.ι (algebraMap F W.FunctionField a - polyToFunctionField W X) := by
    rw [map_sub, D₂.ι.commutes]
  have h1ne : algebraMap F W.FunctionField a - D₁.ι (polyToFunctionField W X) ≠ 0 :=
    h1 ▸ mmr73_cs_iota_ne_zero D₁ (kw_dcao_algebraMap_sub_X_ne_zero a)
  have h2ne : algebraMap F W.FunctionField a - D₂.ι (polyToFunctionField W X) ≠ 0 :=
    h2 ▸ mmr73_cs_iota_ne_zero D₂ (kw_dcao_algebraMap_sub_X_ne_zero a)
  have hVne := kw_dcao_specVert_ne_zero_of_hgm D₁ D₂ D₃ hgm a
  rw [← (placeOfPoint P).ord_mul hLne hL'ne', hprod,
    mmr73_cs_ord_neg (placeOfPoint P),
    (placeOfPoint P).ord_mul (mul_ne_zero h1ne h2ne) hVne,
    (placeOfPoint P).ord_mul h1ne h2ne, h1, h2,
    kw_dcao_ord_Dtransport D₁, kw_dcao_ord_Dtransport D₂,
    kw_dcao_ord_specVert_eq_transport D₁ D₂ D₃ hgm hX a P]

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_dcao_algebraMap_XClass (a : F) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W a)
      = polyToFunctionField W X - algebraMap F W.FunctionField a := by
  rw [show polyToFunctionField W X - algebraMap F W.FunctionField a
    = polyToFunctionField W (X - C a) by rw [map_sub, polyToFunctionField_C],
    polyToFunctionField_apply, CoordinateRing.XClass, algebraMap_polynomial_eq_mk_C]

omit [DecidableEq F] [CharZero F] [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W]
  [W.AbelTheorem] in
theorem kw_dcao_ord_XsubA_eq_one {a b : F} (h : W.Nonsingular a b)
    (hY : W.toAffine.polynomialY.evalEval a b ≠ 0) :
    (placeOfEquation h.left).ord
      (polyToFunctionField W X - algebraMap F W.FunctionField a) = 1 := by
  rw [← kw_dcao_algebraMap_XClass a]
  exact ord_placeOfEquation_XClass_self h.left hY

omit [DecidableEq F] [CharZero F] [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W]
  [W.AbelTheorem] in
theorem kw_dcao_ord_XsubA_eq_two {a b : F} (h : W.Nonsingular a b)
    (hY : W.toAffine.polynomialY.evalEval a b = 0) :
    (placeOfEquation h.left).ord
      (polyToFunctionField W X - algebraMap F W.FunctionField a) = 2 := by
  set q : F[X] := X ^ 2 + C (a + W.a₂) * X + C (a ^ 2 + W.a₂ * a + W.a₄) with hq
  have hFFeq : yGen W ^ 2 + algebraMap F W.FunctionField W.a₁
          * polyToFunctionField W X * yGen W
        + algebraMap F W.FunctionField W.a₃ * yGen W
      = polyToFunctionField W X ^ 3
        + algebraMap F W.FunctionField W.a₂ * polyToFunctionField W X ^ 2
        + algebraMap F W.FunctionField W.a₄ * polyToFunctionField W X
        + algebraMap F W.FunctionField W.a₆ := by
    have heq := es1a6_add_equation W (AlgHom.id F W.FunctionField)
    rw [Affine.equation_iff] at heq
    simp only [AlgHom.id_apply, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq
    linear_combination heq
  have hab : b ^ 2 + W.a₁ * a * b + W.a₃ * b
      = a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆ := by
    have heq := h.left; rw [Affine.equation_iff] at heq; linear_combination heq
  have h2b : (2 : F) * b + W.a₁ * a + W.a₃ = 0 := by
    have := hY; rw [Affine.evalEval_polynomialY] at this; linear_combination this
  have hprod : (yGen W - algebraMap F W.FunctionField b) ^ 2
      = (polyToFunctionField W X - algebraMap F W.FunctionField a)
        * (polyToFunctionField W q
            - algebraMap F W.FunctionField W.a₁ * yGen W) := by
    rw [hq]
    simp only [map_add, map_mul, map_pow, polyToFunctionField_C]
    have hcab := congrArg (algebraMap F W.FunctionField) hab
    simp only [map_add, map_mul, map_pow] at hcab
    have hc2b := congrArg (algebraMap F W.FunctionField) h2b
    simp only [map_add, map_mul, _root_.map_zero, map_ofNat] at hc2b
    linear_combination hFFeq - hcab - (yGen W - algebraMap F W.FunctionField b) * hc2b
  have hYb : (placeOfEquation h.left).ord
      (yGen W - algebraMap F W.FunctionField b) = 1 := by
    have hbr : algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.YClass W (C b))
        = yGen W - algebraMap F W.FunctionField b := by
      rw [CoordinateRing.YClass, map_sub, ← algebraMap_polynomial_eq_mk_C, map_sub,
        ← polyToFunctionField_apply, polyToFunctionField_C]; rfl
    rw [← hbr]
    exact ord_placeOfEquation_YClass_self h.left hY
  have hYbne : yGen W - algebraMap F W.FunctionField b ≠ 0 := fun hc => by
    rw [hc, (placeOfEquation h.left).ord_zero] at hYb; exact one_ne_zero hYb.symm
  set q' : F[X] := q - C (W.a₁ * b) with hq'
  have hq'a : q'.eval a ≠ 0 := by
    have hns := h.2.resolve_right (not_not.mpr hY)
    rw [Affine.evalEval_polynomialX] at hns
    intro hc
    simp only [hq', hq, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hc
    exact hns (by linear_combination -hc)
  have hq'ne : q' ≠ 0 := fun hc => hq'a (by rw [hc, eval_zero])
  have hoq' : (placeOfEquation h.left).ord (polyToFunctionField W q') = 0 :=
    (ord_polyToFunctionField_eq_zero_iff h.left hq'ne).mpr hq'a
  have hrsplit : polyToFunctionField W q - algebraMap F W.FunctionField W.a₁ * yGen W
      = polyToFunctionField W q'
        + (- algebraMap F W.FunctionField W.a₁)
            * (yGen W - algebraMap F W.FunctionField b) := by
    rw [hq', map_sub, polyToFunctionField_C, map_mul]; ring
  have hor : (placeOfEquation h.left).ord
      (polyToFunctionField W q - algebraMap F W.FunctionField W.a₁ * yGen W) = 0 := by
    by_cases ha1 : W.a₁ = 0
    · rw [ha1, _root_.map_zero, zero_mul, sub_zero,
        show q = q' by rw [hq', ha1, zero_mul, C_0, sub_zero]]
      exact hoq'
    · rw [hrsplit,
        (placeOfEquation h.left).ord_add_eq_min
          (polyToFunctionField_ne_zero hq'ne)
          (mul_ne_zero (neg_ne_zero.mpr
            ((map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr ha1)) hYbne)
          (by
            rw [hoq', (placeOfEquation h.left).ord_mul
              (neg_ne_zero.mpr
                ((map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr ha1))
              hYbne, mmr73_cs_ord_neg, AlgebraicCurve.Place.ord_algebraMap (placeOfEquation h.left),
              zero_add,
              hYb]
            exact zero_ne_one),
        hoq', (placeOfEquation h.left).ord_mul
          (neg_ne_zero.mpr
            ((map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr ha1))
          hYbne, mmr73_cs_ord_neg, AlgebraicCurve.Place.ord_algebraMap (placeOfEquation h.left),
            zero_add, hYb]
      exact min_eq_left zero_le_one
  have hrne : polyToFunctionField W q - algebraMap F W.FunctionField W.a₁ * yGen W ≠ 0 := by
    intro hc
    exact hYbne (pow_eq_zero_iff two_ne_zero |>.mp (by rw [hprod, hc, mul_zero]))
  have hXane : polyToFunctionField W X - algebraMap F W.FunctionField a ≠ 0 := by
    rw [← neg_sub, neg_ne_zero]; exact kw_dcao_algebraMap_sub_X_ne_zero a
  have hord := congrArg (placeOfEquation h.left).ord hprod
  rw [show (yGen W - algebraMap F W.FunctionField b) ^ 2
      = (yGen W - algebraMap F W.FunctionField b)
        * (yGen W - algebraMap F W.FunctionField b) from sq _,
    (placeOfEquation h.left).ord_mul hYbne hYbne,
    (placeOfEquation h.left).ord_mul hXane hrne, hor, add_zero, hYb] at hord
  linarith [hord]

omit [CharZero F] [W.AbelTheorem] in
theorem kw_dcao_ord_aSubX_formula {a b : F} (h : W.Nonsingular a b) (Q : W.Point) :
    (placeOfPoint Q).ord (algebraMap F W.FunctionField a - polyToFunctionField W X)
      = (if Q = Point.some a b h then 1 else 0)
        + (if Q = -Point.some a b h then 1 else 0)
        - 2 * (if Q = 0 then 1 else 0) := by
  rw [show algebraMap F W.FunctionField a - polyToFunctionField W X
    = -(polyToFunctionField W X - algebraMap F W.FunctionField a) by ring,
    mmr73_cs_ord_neg, Point.neg_some h,
    show polyToFunctionField W X - algebraMap F W.FunctionField a
      = polyToFunctionField W (X - C a) by rw [map_sub, polyToFunctionField_C]]
  rcases Q with _ | ⟨r, s, h'⟩
  · rw [show (Point.zero : W.Point) = 0 from rfl,
      ite_eq_right (Point.some_ne_zero h).symm,
      ite_eq_right (Point.some_ne_zero ((Affine.nonsingular_neg a b).mpr h)).symm,
      ite_eq_left rfl,
      show placeOfPoint (0 : W.Point) = InfinitePlace.place from rfl,
      (InfinitePlace.place (W := W)).ord_ringHom_eq_natDegree_mul
        polyToFunctionField_injective polyToFunctionField_C
        (ord_X_neg_of_not_isFinitePlace _ InfinitePlace.not_isFinitePlace)
        (X_sub_C_ne_zero a),
      natDegree_X_sub_C,
      ord_X_eq_neg_two_of_not_isFinitePlace _ InfinitePlace.not_isFinitePlace]
    ring
  · simp only [placeOfPoint_some h', ite_eq_right (Point.some_ne_zero h'), mul_zero, sub_zero,
      Point.some.injEq]
    by_cases hra : r = a
    · subst r
      have hsb : s = b ∨ s = W.toAffine.negY a b :=
        Y_eq_of_X_eq h'.left h.left rfl
      simp only [true_and]
      rw [show polyToFunctionField W (X - C a)
        = polyToFunctionField W X - algebraMap F W.FunctionField a by
          rw [map_sub, polyToFunctionField_C]]
      by_cases hYs : W.toAffine.polynomialY.evalEval a s = 0
      · rw [kw_dcao_ord_XsubA_eq_two h' hYs]
        have hss : s = W.toAffine.negY a s := by
          rw [Affine.evalEval_polynomialY] at hYs
          unfold Affine.negY; linear_combination hYs
        rcases hsb with rfl | rfl
        · rw [ite_eq_left rfl, ite_eq_left hss]; rfl
        · rw [ite_eq_left (hss.trans (Affine.negY_negY a b)), ite_eq_left rfl]; rfl
      · rw [kw_dcao_ord_XsubA_eq_one h' hYs]
        have hbne : b ≠ W.toAffine.negY a b := by
          intro hbb
          apply hYs
          have hseb : s = b := hsb.elim id (fun hs => hs.trans hbb.symm)
          subst hseb
          rw [Affine.evalEval_polynomialY]
          have hbb' := hbb; unfold Affine.negY at hbb'
          linear_combination hbb'
        rcases hsb with rfl | rfl
        · rw [ite_eq_left rfl, ite_eq_right hbne, add_zero]
        · rw [ite_eq_right (Ne.symm hbne), ite_eq_left rfl, zero_add]
    · simp only [hra, false_and, ite_false, add_zero]
      exact (ord_polyToFunctionField_eq_zero_iff h'.left (X_sub_C_ne_zero a)).mpr
        (by simp [sub_ne_zero, hra])

variable (W) in
def KwDCAOSpecLineOrdMatchHgm : Prop :=
  ∀ D₁ D₂ D₃ : IsogenyEndDatum W,
    (∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P) →
    D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X) →
      ∀ {a b : F} (h : W.Nonsingular a b),
        kw_dcao_specLine D₁ D₂ a b ≠ 0 ∧
          ∀ P : W.Point,
            (placeOfPoint P).ord (kw_dcao_specLine D₁ D₂ a b)
              = (placeOfPoint (D₁.geomMorph P + D₂.geomMorph P)).ord
                  (algebraMap F W.FunctionField a - polyToFunctionField W X)
                - (((if D₁.geomMorph P + D₂.geomMorph P = Point.some a b h then 1 else 0)
                    - (if D₁.geomMorph P = Point.some a b h then 1 else 0)
                    - (if D₂.geomMorph P = Point.some a b h then 1 else 0))
                  - ((if D₁.geomMorph P + D₂.geomMorph P = 0 then 1 else 0)
                    - (if D₁.geomMorph P = 0 then 1 else 0)
                    - (if D₂.geomMorph P = 0 then 1 else 0)))

variable (W) in
def KwDCAOSpecLineOrdMatchAllAffine : Prop :=
  ∀ D₁ D₂ D₃ : IsogenyEndDatum W,
    (∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P) →
    D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X) →
      ∀ {a b : F} (h : W.Nonsingular a b),
        ¬ b = W.toAffine.negY a b →
          ∀ P : W.Point,
            D₁.geomMorph P ≠ 0 → D₂.geomMorph P ≠ 0 →
              D₁.geomMorph P + D₂.geomMorph P ≠ 0 →
            (placeOfPoint P).ord (kw_dcao_specLine D₁ D₂ a b)
              = (placeOfPoint (D₁.geomMorph P + D₂.geomMorph P)).ord
                  (algebraMap F W.FunctionField a - polyToFunctionField W X)
                - (((if D₁.geomMorph P + D₂.geomMorph P = Point.some a b h then 1 else 0)
                    - (if D₁.geomMorph P = Point.some a b h then 1 else 0)
                    - (if D₂.geomMorph P = Point.some a b h then 1 else 0))
                  - ((if D₁.geomMorph P + D₂.geomMorph P = 0 then 1 else 0)
                    - (if D₁.geomMorph P = 0 then 1 else 0)
                    - (if D₂.geomMorph P = 0 then 1 else 0)))

theorem kw_dcao_specLineOrdMatch_hgm_of_allAffine
    (hAA : KwDCAOSpecLineOrdMatchAllAffine W) :
    KwDCAOSpecLineOrdMatchHgm W := by
  intro D₁ D₂ D₃ hgm hX a b h
  refine ⟨kw_dcao_specLine_ne_zero_of_hgm D₁ D₂ D₃ hgm hX h, fun P => ?_⟩
  have hLne := kw_dcao_specLine_ne_zero_of_hgm D₁ D₂ D₃ hgm hX h
  have hL'ne : kw_dcao_specLine D₁ D₂ a (W.toAffine.negY a b) ≠ 0 :=
    kw_dcao_specLine_ne_zero_of_hgm D₁ D₂ D₃ hgm hX ((Affine.nonsingular_neg a b).mpr h)
  have hSum := kw_dcao_specLine_ord_sum D₁ D₂ D₃ hgm hX h P
  rw [kw_dcao_ord_aSubX_formula h (D₁.geomMorph P),
    kw_dcao_ord_aSubX_formula h (D₂.geomMorph P),
    kw_dcao_ord_aSubX_formula h (D₁.geomMorph P + D₂.geomMorph P)] at hSum
  rw [kw_dcao_ord_aSubX_formula h (D₁.geomMorph P + D₂.geomMorph P)]
  set Q₁ := D₁.geomMorph P with hQ1def
  set Q₂ := D₂.geomMorph P with hQ2def
  set L := Point.some a b h with hLdef
  set u := (placeOfPoint P).ord (kw_dcao_specLine D₁ D₂ a b) with hu
  set v := (placeOfPoint P).ord (kw_dcao_specLine D₁ D₂ a (W.toAffine.negY a b)) with hv
  set l₁ : ℤ := if Q₁ = L then 1 else 0 with hl1d
  set m₁ : ℤ := if Q₁ = -L then 1 else 0 with hm1d
  set e₁ : ℤ := if Q₁ = 0 then 1 else 0 with he1d
  set l₂ : ℤ := if Q₂ = L then 1 else 0 with hl2d
  set m₂ : ℤ := if Q₂ = -L then 1 else 0 with hm2d
  set e₂ : ℤ := if Q₂ = 0 then 1 else 0 with he2d
  set l₁₂ : ℤ := if Q₁ + Q₂ = L then 1 else 0 with hl12d
  set m₁₂ : ℤ := if Q₁ + Q₂ = -L then 1 else 0 with hm12d
  set e₁₂ : ℤ := if Q₁ + Q₂ = 0 then 1 else 0 with he12d
  by_cases hκ : b = W.toAffine.negY a b
  · have huveq : u = v := by rw [hu, hv, ← hκ]
    have hLL : L = -L := by
      rw [hLdef, Point.neg_some h]
      simp only [Point.some.injEq, true_and]; exact hκ
    have hmL1 : m₁ = l₁ := by rw [hm1d, hl1d, ← hLL]
    have hmL2 : m₂ = l₂ := by rw [hm2d, hl2d, ← hLL]
    have hmL12 : m₁₂ = l₁₂ := by rw [hm12d, hl12d, ← hLL]
    omega
  · have hκne : algebraMap F W.FunctionField (b - W.toAffine.negY a b) ≠ 0 :=
      fun hc => hκ (sub_eq_zero.mp
        ((algebraMap F W.FunctionField).injective (by rw [hc, _root_.map_zero])))
    have hLneL' : L ≠ -L := fun hc => by
      rw [hLdef, Point.neg_some h] at hc
      simp only [Point.some.injEq, true_and] at hc; exact hκ hc
    have hLne0 : L ≠ 0 := Point.some_ne_zero h
    have hL'ne0 : -L ≠ 0 := neg_ne_zero.mpr hLne0
    have hdiff := kw_dcao_specLine_negY_diff D₁ D₂ a b
    have hκord : (placeOfPoint P).ord
        (algebraMap F W.FunctionField (b - W.toAffine.negY a b)) = 0 :=
      AlgebraicCurve.Place.ord_algebraMap (placeOfPoint P) _
    have huv : u ≠ 0 → v = min u 0 := by
      intro hune
      have heq : kw_dcao_specLine D₁ D₂ a (W.toAffine.negY a b)
          = kw_dcao_specLine D₁ D₂ a b
            + -(algebraMap F W.FunctionField (b - W.toAffine.negY a b)) := by
        rw [← hdiff]; ring
      rw [hv, heq, (placeOfPoint P).ord_add_eq_min hLne (neg_ne_zero.mpr hκne)
        (by rw [mmr73_cs_ord_neg, hκord]; exact hune), mmr73_cs_ord_neg, hκord, ← hu]
    have hvu : v ≠ 0 → u = min v 0 := by
      intro hvne
      have heq : kw_dcao_specLine D₁ D₂ a b
          = kw_dcao_specLine D₁ D₂ a (W.toAffine.negY a b)
            + algebraMap F W.FunctionField (b - W.toAffine.negY a b) := by
        rw [← hdiff]; ring
      rw [hu, heq, (placeOfPoint P).ord_add_eq_min hL'ne hκne
        (by rw [hκord]; exact hvne), hκord, ← hv]
    have hbnd : ∀ Q : W.Point,
        (if Q = L then (1:ℤ) else 0) + (if Q = -L then (1:ℤ) else 0)
            + (if Q = 0 then (1:ℤ) else 0) ≤ 1
          ∧ (0:ℤ) ≤ (if Q = L then (1:ℤ) else 0)
          ∧ (0:ℤ) ≤ (if Q = -L then (1:ℤ) else 0)
          ∧ (0:ℤ) ≤ (if Q = 0 then (1:ℤ) else 0) := by
      intro Q
      refine ⟨?_, by split_ifs <;> omega, by split_ifs <;> omega,
        by split_ifs <;> omega⟩
      by_cases hQL : Q = L
      · rw [ite_eq_left hQL, ite_eq_right (hQL ▸ hLneL'), ite_eq_right (hQL ▸ hLne0)]; omega
      · by_cases hQL' : Q = -L
        · rw [ite_eq_right hQL, ite_eq_left hQL', ite_eq_right (hQL' ▸ hL'ne0)]; omega
        · rw [ite_eq_right hQL, ite_eq_right hQL']; split_ifs <;> omega
    have hb1 : l₁ + m₁ + e₁ ≤ 1 ∧ 0 ≤ l₁ ∧ 0 ≤ m₁ ∧ 0 ≤ e₁ := by
      rw [hl1d, hm1d, he1d]; exact hbnd Q₁
    have hb2 : l₂ + m₂ + e₂ ≤ 1 ∧ 0 ≤ l₂ ∧ 0 ≤ m₂ ∧ 0 ≤ e₂ := by
      rw [hl2d, hm2d, he2d]; exact hbnd Q₂
    have hb12 : l₁₂ + m₁₂ + e₁₂ ≤ 1 ∧ 0 ≤ l₁₂ ∧ 0 ≤ m₁₂ ∧ 0 ≤ e₁₂ := by
      rw [hl12d, hm12d, he12d]; exact hbnd (Q₁+Q₂)
    by_cases hQ1z : Q₁ = 0
    · have hge : e₁ = 1 := by rw [he1d, ite_eq_left hQ1z]
      have hgl12 : l₁₂ = l₂ := by rw [hl12d, hl2d, hQ1z, zero_add]
      have hgm12 : m₁₂ = m₂ := by rw [hm12d, hm2d, hQ1z, zero_add]
      have hge12 : e₁₂ = e₂ := by rw [he12d, he2d, hQ1z, zero_add]
      omega
    by_cases hQ2z : Q₂ = 0
    · have hge : e₂ = 1 := by rw [he2d, ite_eq_left hQ2z]
      have hgl12 : l₁₂ = l₁ := by rw [hl12d, hl1d, hQ2z, add_zero]
      have hgm12 : m₁₂ = m₁ := by rw [hm12d, hm1d, hQ2z, add_zero]
      have hge12 : e₁₂ = e₁ := by rw [he12d, he1d, hQ2z, add_zero]
      omega
    by_cases hQ12z : Q₁ + Q₂ = 0
    · have hge : e₁₂ = 1 := by rw [he12d, ite_eq_left hQ12z]
      have hQ2neg : Q₂ = -Q₁ := (neg_eq_of_add_eq_zero_right hQ12z).symm
      have hgl2 : l₂ = m₁ := by
        rw [hl2d, hm1d]; congr 1
        exact propext ⟨fun h' => by rw [hQ2neg] at h'; rw [← h', neg_neg],
          fun h' => by rw [hQ2neg, h', neg_neg]⟩
      have hgm2 : m₂ = l₁ := by
        rw [hm2d, hl1d]; congr 1
        exact propext ⟨fun h' => by rw [hQ2neg] at h'; exact neg_inj.mp h',
          fun h' => by rw [hQ2neg, h']⟩
      have hge2 : e₂ = e₁ := by
        rw [he2d, he1d]; congr 1
        exact propext ⟨fun h' => by rw [hQ2neg] at h'; exact neg_eq_zero.mp h',
          fun h' => by rw [hQ2neg, h', _root_.neg_zero]⟩
      omega
    have := hAA D₁ D₂ D₃ hgm hX h hκ P (hQ1def ▸ hQ1z) (hQ2def ▸ hQ2z)
      (hQ1def ▸ hQ2def ▸ hQ12z)
    rw [kw_dcao_ord_aSubX_formula h (D₁.geomMorph P + D₂.geomMorph P)] at this
    simp only [← hQ1def, ← hQ2def, ← hLdef] at this
    linarith [this]

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

open ModularCurve.Es1a1
open ModularCurve.Mmr73
namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

attribute [local instance] ModularCurve.Es1a1.instDecEqFunctionFieldEs1a6Add

theorem kw_dcao_sumDatum_Y_of_hgm (D₁ D₂ D₃ : IsogenyEndDatum W)
    (hgm : ∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P)
    (hX : D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X)) :
    ∃ Ds : IsogenyEndDatum W,
      Ds.ι (polyToFunctionField W X) = es1a6_addSumX W D₁.ι D₂.ι
      ∧ Ds.ι (yGen W) = es1a6_addSumY W D₁.ι D₂.ι
      ∧ ∀ P, Ds.geomMorph P = D₁.geomMorph P + D₂.geomMorph P := by
  have _pin := Classical.em True
  have hnc := kw_dcao_addSumX_nonconst_of_hgm D₁ D₂ D₃ hgm
  have hcol : ¬ es1a6_addCollapse W D₁.ι D₂.ι :=
    es1a6_add_not_collapse_of_X_ne W D₁.ι D₂.ι hX
  have htr : Function.Injective
      (Polynomial.aeval (R := F) (es1a6_addSumX W D₁.ι D₂.ι)) :=
    es1a6_add_aeval_sumX_injective_of_forall_ne W D₁.ι D₂.ι hnc
  obtain ⟨hι, hfin⟩ := kw_hk5f_addIntegralFiniteDataAt_proved W D₁ D₂ hcol htr
  refine ⟨⟨es1a6_addSumPullbackHom W D₁.ι D₂.ι hcol htr, hι, hfin⟩,
    es1a6_addSumPullbackHom_X W D₁.ι D₂.ι hcol htr,
    es1a6_addSumPullbackHom_yGen W D₁.ι D₂.ι hcol htr, fun P => ?_⟩
  have h1 := kw_coordSeamDataAt_geomMorph D₁ P
  have h2 := kw_coordSeamDataAt_geomMorph D₂ P
  have hsum := kw_hk5f_addSumCoordSeamDataNCAt_proved W D₁.ι D₂.ι hcol hnc
    (placeOfPoint P) (D₁.geomMorph P) (D₂.geomMorph P) h1 h2
  have hseam := es1a6_addSumSeam_of_data D₁.ι D₂.ι hcol htr hι P
    (D₁.geomMorph P + D₂.geomMorph P) hsum
  exact placeOfPoint_injective
    (((⟨_, hι, hfin⟩ : IsogenyEndDatum W).placeOfPoint_geomMorph P).symm.trans hseam)

theorem kw_dcao_specLineOrdMatch_allAffine_proved :
    KwDCAOSpecLineOrdMatchAllAffine W := by
  have _pin := Classical.em True
  intro D₁ D₂ D₃ hgm hX a b h hκ P hQ1 hQ2 hQ12
  have hrat : (placeOfPoint P).IsRational :=
    (placeOfPoint P).isRational_of_deg_eq_one (deg_placeOfPoint P)
  set x₁ := D₁.ι (polyToFunctionField W X) with hx1d
  set x₂ := D₂.ι (polyToFunctionField W X) with hx2d
  set y₁ := D₁.ι (yGen W) with hy1d
  set y₂ := D₂.ι (yGen W) with hy2d
  set Λ := kw_dcao_lineSlope D₁ D₂ with hΛd
  have hXne : x₁ ≠ x₂ := hX
  have hδne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hXne
  set b' := W.toAffine.negY a b with hb'd
  have hLne := kw_dcao_specLine_ne_zero_of_hgm D₁ D₂ D₃ hgm hX h
  have hL'ne : kw_dcao_specLine D₁ D₂ a b' ≠ 0 :=
    kw_dcao_specLine_ne_zero_of_hgm D₁ D₂ D₃ hgm hX
      ((Affine.nonsingular_neg a b).mpr h)
  have hVne := kw_dcao_specVert_ne_zero_of_hgm D₁ D₂ D₃ hgm a
  have hmemOfD : ∀ (D : IsogenyEndDatum W) {r s hns},
      D.geomMorph P = Point.some r s hns →
      D.ι (polyToFunctionField W X) ∈ (placeOfPoint P).toValuationSubring
        ∧ D.ι (yGen W) ∈ (placeOfPoint P).toValuationSubring := by
    intro D r s hns hDeq
    have hmem : ∀ g : W.CoordinateRing,
        D.ι (algebraMap _ _ g) ∈ (placeOfPoint P).toValuationSubring := by
      intro g
      rcases eq_or_ne (D.ι (algebraMap _ _ g)) 0 with h0 | hne
      · exact h0 ▸ zero_mem _
      · refine AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfPoint P) hne ?_
        rw [kw_dcao_ord_Dtransport D, hDeq, placeOfPoint_some]
        exact ord_placeOfEquation_nonneg hns.left g
    exact ⟨by rw [polyToFunctionField_apply, algebraMap_polynomial_eq_mk_C]; exact hmem _,
      hmem _⟩
  obtain ⟨r₁, s₁, hns₁, hQ1eq⟩ : ∃ r s hns, D₁.geomMorph P = Point.some r s hns := by
    rcases hQ : D₁.geomMorph P with _ | ⟨r, s, hns⟩
    · exact absurd (show D₁.geomMorph P = 0 by exact_mod_cast hQ) hQ1
    · exact ⟨r, s, hns, rfl⟩
  obtain ⟨r₂, s₂, hns₂, hQ2eq⟩ : ∃ r s hns, D₂.geomMorph P = Point.some r s hns := by
    rcases hQ : D₂.geomMorph P with _ | ⟨r, s, hns⟩
    · exact absurd (show D₂.geomMorph P = 0 by exact_mod_cast hQ) hQ2
    · exact ⟨r, s, hns, rfl⟩
  obtain ⟨hx1m, hy1m⟩ := hmemOfD D₁ hQ1eq
  obtain ⟨hx2m, hy2m⟩ := hmemOfD D₂ hQ2eq
  obtain ⟨hex1, hey1⟩ := mmr73_cs_geomMorph_some_coords D₁ P hQ1eq hx1m hy1m
  obtain ⟨hex2, hey2⟩ := mmr73_cs_geomMorph_some_coords D₂ P hQ2eq hx2m hy2m
  rw [← hx1d] at hx1m hex1; rw [← hy1d] at hy1m hey1
  rw [← hx2d] at hx2m hex2; rw [← hy2d] at hy2m hey2
  obtain ⟨Ds, hXs, hYs, hgms⟩ := kw_dcao_sumDatum_Y_of_hgm D₁ D₂ D₃ hgm hX
  obtain ⟨rs, ss, hnss, hQseq⟩ : ∃ r s hns, Ds.geomMorph P = Point.some r s hns := by
    rcases hQ : Ds.geomMorph P with _ | ⟨r, s, hns⟩
    · exact absurd ((hgms P).symm.trans (show Ds.geomMorph P = 0 by exact_mod_cast hQ)) hQ12
    · exact ⟨r, s, hns, rfl⟩
  obtain ⟨hxsm, hysm⟩ := hmemOfD Ds hQseq
  obtain ⟨hexs, heys⟩ := mmr73_cs_geomMorph_some_coords Ds P hQseq hxsm hysm
  rw [hXs] at hexs hxsm; rw [hYs] at heys hysm
  have hQsum : D₁.geomMorph P + D₂.geomMorph P = Point.some rs ss hnss :=
    (hgms P).symm.trans hQseq
  have hΛeq : Λ = (y₁ - y₂) / (x₁ - x₂) := Affine.slope_of_X_ne hXne
  have hΛδ : Λ * (x₁ - x₂) = y₁ - y₂ := by rw [hΛeq, div_mul_cancel₀ _ hδne]
  set σ := y₁ + y₂ + algebraMap F W.FunctionField W.a₁ * x₁
      + algebraMap F W.FunctionField W.a₃ with hσd
  have ha1m : algebraMap F W.FunctionField W.a₁
      ∈ (placeOfPoint P).toValuationSubring := (placeOfPoint P).algebraMap_mem' W.a₁
  have ha3m : algebraMap F W.FunctionField W.a₃
      ∈ (placeOfPoint P).toValuationSubring := (placeOfPoint P).algebraMap_mem' W.a₃
  have hcsub : ∃ ξ, Λ * σ = ξ ∧ ξ ∈ (placeOfPoint P).toValuationSubring := by
    set ξ' := x₁ * x₁ + x₁ * x₂ + x₂ * x₂
        + algebraMap F W.FunctionField W.a₂ * (x₁ + x₂)
        + algebraMap F W.FunctionField W.a₄
        - algebraMap F W.FunctionField W.a₁ * y₂ with hξd
    refine ⟨ξ', ?_, ?_⟩
    · have hE₁ := es1a6_add_equation W D₁.ι
      have hE₂ := es1a6_add_equation W D₂.ι
      rw [Affine.equation_iff] at hE₁ hE₂
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄,
        WeierstrassCurve.map_a₆, ← hx1d, ← hy1d] at hE₁
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄,
        WeierstrassCurve.map_a₆, ← hx2d, ← hy2d] at hE₂
      have hcub : (y₁ - y₂) * σ = (x₁ - x₂) * ξ' := by
        rw [hσd, hξd]; linear_combination hE₁ - hE₂
      have heq : (x₁ - x₂) * (Λ * σ) = (x₁ - x₂) * ξ' := by
        rw [← mul_assoc, mul_comm (x₁ - x₂) Λ, hΛδ, hcub]
      exact mul_left_cancel₀ hδne heq
    · rw [hξd]
      exact sub_mem (add_mem (add_mem (add_mem (add_mem (mul_mem hx1m hx1m)
        (mul_mem hx1m hx2m)) (mul_mem hx2m hx2m))
        (mul_mem ((placeOfPoint P).algebraMap_mem' _) (add_mem hx1m hx2m)))
        ((placeOfPoint P).algebraMap_mem' _))
        (mul_mem ha1m hy2m)
  obtain ⟨ξ, hΛσ, hξm⟩ := hcsub
  have hσm : σ ∈ (placeOfPoint P).toValuationSubring :=
    add_mem (add_mem (add_mem hy1m hy2m) (mul_mem ha1m hx1m)) ha3m
  have hδm : x₁ - x₂ ∈ (placeOfPoint P).toValuationSubring := sub_mem hx1m hx2m
  have hy12m : y₁ - y₂ ∈ (placeOfPoint P).toValuationSubring := sub_mem hy1m hy2m
  have hevz : ∀ {f}, f ∈ (placeOfPoint P).toValuationSubring →
      0 < (placeOfPoint P).ord f → (placeOfPoint P).evalAt f = 0 := fun hfm hpos =>
    mmr73_cs_evalAt_eq_of_ord_sub_pos (placeOfPoint P) hrat hfm
      (a := 0) (by rwa [_root_.map_zero, sub_zero])
  have hopz : ∀ {f}, f ≠ 0 → f ∈ (placeOfPoint P).toValuationSubring →
      (placeOfPoint P).evalAt f = 0 → 0 < (placeOfPoint P).ord f := fun hfne hfm he0 =>
    lt_of_le_of_ne (AlgebraicCurve.Place.ord_nonneg_of_mem (placeOfPoint P) hfm)
      (fun h0 => (placeOfPoint P).evalAt_ne_zero hrat hfne h0.symm he0)
  have hnotBoth : (placeOfPoint P).evalAt (x₁ - x₂) ≠ 0
      ∨ (placeOfPoint P).evalAt σ ≠ 0 := by
    rw [or_iff_not_imp_left, not_not]; intro hδ0
    rw [(placeOfPoint P).evalAt_sub hrat hx1m hx2m, hex1, hex2, sub_eq_zero] at hδ0
    intro hσ0
    rw [hσd, (placeOfPoint P).evalAt_add hrat
        (add_mem (add_mem hy1m hy2m) (mul_mem ha1m hx1m)) ha3m,
      (placeOfPoint P).evalAt_add hrat (add_mem hy1m hy2m) (mul_mem ha1m hx1m),
      (placeOfPoint P).evalAt_add hrat hy1m hy2m,
      (placeOfPoint P).evalAt_mul hrat ha1m hx1m, hey1, hey2, hex1,
      (placeOfPoint P).evalAt_algebraMap, (placeOfPoint P).evalAt_algebraMap] at hσ0
    refine hQ12 ?_
    rw [hQ1eq, hQ2eq]
    exact Point.add_of_Y_eq hδ0
      (by unfold Affine.negY; linear_combination hσ0 - W.a₁ * hδ0)
  have hΛm : Λ ∈ (placeOfPoint P).toValuationSubring := by
    rcases hnotBoth with hδnz | hσnz
    · have hδord : (placeOfPoint P).ord (x₁ - x₂) = 0 := by
        by_contra hne; exact hδnz (hevz hδm (lt_of_le_of_ne
          (AlgebraicCurve.Place.ord_nonneg_of_mem (placeOfPoint P) hδm) (Ne.symm hne)))
      have hδinv : (x₁ - x₂)⁻¹ ∈ (placeOfPoint P).toValuationSubring :=
        AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfPoint P) (inv_ne_zero hδne)
          (by rw [(placeOfPoint P).ord_inv, hδord]; omega)
      rw [hΛeq, div_eq_mul_inv]; exact mul_mem hy12m hδinv
    · have hσne : σ ≠ 0 := fun h0 => hσnz (h0 ▸ (placeOfPoint P).evalAt_zero)
      have hσord : (placeOfPoint P).ord σ = 0 := by
        by_contra hne; exact hσnz (hevz hσm (lt_of_le_of_ne
          (AlgebraicCurve.Place.ord_nonneg_of_mem (placeOfPoint P) hσm) (Ne.symm hne)))
      have hσinv : σ⁻¹ ∈ (placeOfPoint P).toValuationSubring :=
        AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfPoint P) (inv_ne_zero hσne)
          (by rw [(placeOfPoint P).ord_inv, hσord]; omega)
      rw [show Λ = ξ * σ⁻¹ by field_simp; linear_combination hΛσ]
      exact mul_mem hξm hσinv
  set u := (placeOfPoint P).ord (kw_dcao_specLine D₁ D₂ a b) with hud
  set v := (placeOfPoint P).ord (kw_dcao_specLine D₁ D₂ a b') with hvd
  have hLform1 : ∀ c : F, kw_dcao_specLine D₁ D₂ a c
      = (algebraMap F W.FunctionField c - y₁)
        - Λ * (algebraMap F W.FunctionField a - x₁) := by
    intro c
    change (_ - _ - _ : W.FunctionField) = _
    rw [show kw_dcao_lineIntercept D₁ D₂ = y₁ - Λ * x₁ from rfl]; ring
  have hLform2 : ∀ c : F, kw_dcao_specLine D₁ D₂ a c
      = (algebraMap F W.FunctionField c - y₂)
        - Λ * (algebraMap F W.FunctionField a - x₂) := by
    intro c; rw [hLform1 c]; linear_combination hΛδ
  have hLform3 : ∀ c : F, kw_dcao_specLine D₁ D₂ a c
      = (es1a6_addSumY W D₁.ι D₂.ι + algebraMap F W.FunctionField (c + W.a₃)
          + algebraMap F W.FunctionField W.a₁ * es1a6_addSumX W D₁.ι D₂.ι)
        - Λ * (algebraMap F W.FunctionField a - es1a6_addSumX W D₁.ι D₂.ι) := by
    intro c; rw [hLform1 c]
    simp only [es1a6_addSumY, es1a6_addSumX, ← hx1d, ← hx2d, ← hy1d, ← hy2d,
      Affine.addY, Affine.negY, Affine.negAddY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      map_add]
    ring
  have ham : algebraMap F W.FunctionField a
      ∈ (placeOfPoint P).toValuationSubring := (placeOfPoint P).algebraMap_mem' a
  have hLmem : ∀ c : F, kw_dcao_specLine D₁ D₂ a c
      ∈ (placeOfPoint P).toValuationSubring := fun c => by
    rw [hLform1 c]
    exact sub_mem (sub_mem ((placeOfPoint P).algebraMap_mem' c) hy1m)
      (mul_mem hΛm (sub_mem ham hx1m))
  have hunn : 0 ≤ u := AlgebraicCurve.Place.ord_nonneg_of_mem (placeOfPoint P) (hLmem b)
  have hvnn : 0 ≤ v := AlgebraicCurve.Place.ord_nonneg_of_mem (placeOfPoint P) (hLmem b')
  have hκne : algebraMap F W.FunctionField (b - b') ≠ 0 :=
    fun hc => hκ (sub_eq_zero.mp
      ((algebraMap F W.FunctionField).injective (by rw [hc, _root_.map_zero])))
  have hdiff := kw_dcao_specLine_negY_diff D₁ D₂ a b
  have hκord : (placeOfPoint P).ord (algebraMap F W.FunctionField (b - b')) = 0 :=
    AlgebraicCurve.Place.ord_algebraMap (placeOfPoint P) _
  have huv0 : u = 0 ∨ v = 0 := by
    by_contra hno; rw [not_or] at hno
    have hup : 0 < u := lt_of_le_of_ne hunn (Ne.symm hno.1)
    have heq : kw_dcao_specLine D₁ D₂ a b'
        = kw_dcao_specLine D₁ D₂ a b
          + -(algebraMap F W.FunctionField (b - b')) := by rw [← hdiff]; ring
    have hvcalc : v = min u 0 := by
      rw [hvd, heq, (placeOfPoint P).ord_add_eq_min hLne (neg_ne_zero.mpr hκne)
        (by rw [mmr73_cs_ord_neg, hκord]; exact hno.1),
        mmr73_cs_ord_neg, hκord, ← hud]
    omega
  set L := Point.some a b h with hLdef
  have hnegL : -L = Point.some a b' ((Affine.nonsingular_neg a b).mpr h) := by
    rw [hLdef, Point.neg_some]
  have hforce : ∀ (xj yj : W.FunctionField)
      (hxjm : xj ∈ (placeOfPoint P).toValuationSubring)
      (hyjm : yj ∈ (placeOfPoint P).toValuationSubring)
      (hexj : (placeOfPoint P).evalAt xj = a)
      (c : F)
      (heyj : (placeOfPoint P).evalAt yj = c)
      (hform : kw_dcao_specLine D₁ D₂ a c
        = (algebraMap F W.FunctionField c - yj)
          - Λ * (algebraMap F W.FunctionField a - xj)),
      (placeOfPoint P).evalAt (kw_dcao_specLine D₁ D₂ a c) = 0 := by
    intro xj yj hxjm hyjm hexj c heyj hform
    rw [hform,
      (placeOfPoint P).evalAt_sub hrat
        (sub_mem ((placeOfPoint P).algebraMap_mem' c) hyjm)
        (mul_mem hΛm (sub_mem ham hxjm)),
      (placeOfPoint P).evalAt_sub hrat ((placeOfPoint P).algebraMap_mem' c) hyjm,
      (placeOfPoint P).evalAt_mul hrat hΛm (sub_mem ham hxjm),
      (placeOfPoint P).evalAt_sub hrat ham hxjm,
      (placeOfPoint P).evalAt_algebraMap, (placeOfPoint P).evalAt_algebraMap,
      heyj, hexj, sub_self, sub_self, mul_zero, sub_zero]
  have hZF1 : D₁.geomMorph P ≠ L ∨ 0 < u := by
    rcases eq_or_ne (D₁.geomMorph P) L with heq | hne
    · right
      rw [hQ1eq, hLdef] at heq
      simp only [Point.some.injEq] at heq
      exact hopz hLne (hLmem b)
        (hforce x₁ y₁ hx1m hy1m (hex1.trans heq.1) b (hey1.trans heq.2)
          (hLform1 b))
    · left; exact hne
  have hZF2 : D₂.geomMorph P ≠ L ∨ 0 < u := by
    rcases eq_or_ne (D₂.geomMorph P) L with heq | hne
    · right
      rw [hQ2eq, hLdef] at heq
      simp only [Point.some.injEq] at heq
      exact hopz hLne (hLmem b)
        (hforce x₂ y₂ hx2m hy2m (hex2.trans heq.1) b (hey2.trans heq.2)
          (hLform2 b))
    · left; exact hne
  have hZF1' : D₁.geomMorph P ≠ -L ∨ 0 < v := by
    rcases eq_or_ne (D₁.geomMorph P) (-L) with heq | hne
    · right
      rw [hQ1eq, hnegL] at heq
      simp only [Point.some.injEq] at heq
      exact hopz hL'ne (hLmem b')
        (hforce x₁ y₁ hx1m hy1m (hex1.trans heq.1) b' (hey1.trans heq.2)
          (hLform1 b'))
    · left; exact hne
  have hZF2' : D₂.geomMorph P ≠ -L ∨ 0 < v := by
    rcases eq_or_ne (D₂.geomMorph P) (-L) with heq | hne
    · right
      rw [hQ2eq, hnegL] at heq
      simp only [Point.some.injEq] at heq
      exact hopz hL'ne (hLmem b')
        (hforce x₂ y₂ hx2m hy2m (hex2.trans heq.1) b' (hey2.trans heq.2)
          (hLform2 b'))
    · left; exact hne
  have hbb' : b + b' + W.a₁ * a + W.a₃ = 0 := by
    rw [hb'd]; unfold Affine.negY; ring
  have hforce3 : ∀ c : F, rs = a → ss + c + W.a₁ * a + W.a₃ = 0 →
      (placeOfPoint P).evalAt (kw_dcao_specLine D₁ D₂ a c) = 0 := by
    intro c hrsa hssc
    rw [hLform3 c,
      (placeOfPoint P).evalAt_sub hrat
        (add_mem (add_mem hysm ((placeOfPoint P).algebraMap_mem' _))
          (mul_mem ha1m hxsm))
        (mul_mem hΛm (sub_mem ham hxsm)),
      (placeOfPoint P).evalAt_add hrat
        (add_mem hysm ((placeOfPoint P).algebraMap_mem' _)) (mul_mem ha1m hxsm),
      (placeOfPoint P).evalAt_add hrat hysm ((placeOfPoint P).algebraMap_mem' _),
      (placeOfPoint P).evalAt_mul hrat ha1m hxsm,
      (placeOfPoint P).evalAt_mul hrat hΛm (sub_mem ham hxsm),
      (placeOfPoint P).evalAt_sub hrat ham hxsm,
      (placeOfPoint P).evalAt_algebraMap, (placeOfPoint P).evalAt_algebraMap,
      (placeOfPoint P).evalAt_algebraMap,
      heys, hexs, hrsa, sub_self, mul_zero, sub_zero]
    linear_combination hssc
  have hZF12 : D₁.geomMorph P + D₂.geomMorph P ≠ L ∨ 0 < v := by
    rcases eq_or_ne (D₁.geomMorph P + D₂.geomMorph P) L with heq | hne
    · right
      rw [hQsum, hLdef] at heq
      simp only [Point.some.injEq] at heq
      refine hopz hL'ne (hLmem b') (hforce3 b' heq.1 ?_)
      linear_combination hbb' + heq.2
    · left; exact hne
  have hZF12' : D₁.geomMorph P + D₂.geomMorph P ≠ -L ∨ 0 < u := by
    rcases eq_or_ne (D₁.geomMorph P + D₂.geomMorph P) (-L) with heq | hne
    · right
      rw [hQsum, hnegL] at heq
      simp only [Point.some.injEq] at heq
      refine hopz hLne (hLmem b) (hforce3 b heq.1 ?_)
      linear_combination hbb' + heq.2
    · left; exact hne
  have hSum := kw_dcao_specLine_ord_sum D₁ D₂ D₃ hgm hX h P
  rw [kw_dcao_ord_aSubX_formula h (D₁.geomMorph P),
    kw_dcao_ord_aSubX_formula h (D₂.geomMorph P),
    kw_dcao_ord_aSubX_formula h (D₁.geomMorph P + D₂.geomMorph P)] at hSum
  simp only [ite_eq_right hQ1, ite_eq_right hQ2, ite_eq_right hQ12, mul_zero, sub_zero,
    ← hb'd] at hSum
  rw [kw_dcao_ord_aSubX_formula h (D₁.geomMorph P + D₂.geomMorph P),
    ite_eq_right hQ1, ite_eq_right hQ2, ite_eq_right hQ12]
  simp only [mul_zero, sub_zero, ← hLdef, ← hud, ← hvd] at hSum ⊢
  set l₁ : ℤ := if D₁.geomMorph P = L then 1 else 0 with hl1d
  set m₁ : ℤ := if D₁.geomMorph P = -L then 1 else 0 with hm1d
  set l₂ : ℤ := if D₂.geomMorph P = L then 1 else 0 with hl2d
  set m₂ : ℤ := if D₂.geomMorph P = -L then 1 else 0 with hm2d
  set l₁₂ : ℤ := if D₁.geomMorph P + D₂.geomMorph P = L then 1 else 0 with hl12d
  set m₁₂ : ℤ := if D₁.geomMorph P + D₂.geomMorph P = -L then 1 else 0 with hm12d
  have hF1 : l₁ = 0 ∨ 0 < u := hZF1.imp (fun h => by rw [hl1d, ite_eq_right h]) id
  have hF2 : l₂ = 0 ∨ 0 < u := hZF2.imp (fun h => by rw [hl2d, ite_eq_right h]) id
  have hF1' : m₁ = 0 ∨ 0 < v := hZF1'.imp (fun h => by rw [hm1d, ite_eq_right h]) id
  have hF2' : m₂ = 0 ∨ 0 < v := hZF2'.imp (fun h => by rw [hm2d, ite_eq_right h]) id
  have hF12 : l₁₂ = 0 ∨ 0 < v := hZF12.imp (fun h => by rw [hl12d, ite_eq_right h]) id
  have hF12' : m₁₂ = 0 ∨ 0 < u := hZF12'.imp (fun h => by rw [hm12d, ite_eq_right h]) id
  have hb1 : 0 ≤ l₁ ∧ 0 ≤ m₁ := ⟨by rw [hl1d]; split_ifs <;> omega,
    by rw [hm1d]; split_ifs <;> omega⟩
  have hb2 : 0 ≤ l₂ ∧ 0 ≤ m₂ := ⟨by rw [hl2d]; split_ifs <;> omega,
    by rw [hm2d]; split_ifs <;> omega⟩
  have hb12 : 0 ≤ l₁₂ ∧ 0 ≤ m₁₂ := ⟨by rw [hl12d]; split_ifs <;> omega,
    by rw [hm12d]; split_ifs <;> omega⟩
  clear_value u v l₁ m₁ l₂ m₂ l₁₂ m₁₂
  clear * - hSum hF1 hF2 hF1' hF2' hF12 hF12' hb1 hb2 hb12 huv0 hunn hvnn
  omega

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

local instance kw_dcao_wire_instHPD : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField _

abbrev kw_dcao_specExplicit (D₁ D₂ : IsogenyEndDatum W) (a b : F) : W.FunctionField :=
  kw_dcao_specVert D₁ D₂ a * (kw_dcao_specLine D₁ D₂ a b)⁻¹

theorem kw_dcao_defect_pointDivisor_coeff (D₁ D₂ D₃ : IsogenyEndDatum W)
    (hgm : ∀ P, D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P) (L P : W.Point) :
    (Divisor.pullbackAlong D₃.ι D₃.hι
        (pointDivisor L : Divisor F W.FunctionField)
      - (Divisor.pullbackAlong D₁.ι D₁.hι
            (pointDivisor L : Divisor F W.FunctionField)
          + Divisor.pullbackAlong D₂.ι D₂.hι
            (pointDivisor L : Divisor F W.FunctionField)))
      (placeOfPoint P)
      = ((if D₁.geomMorph P + D₂.geomMorph P = L then 1 else 0)
          - (if D₁.geomMorph P = L then 1 else 0)
          - (if D₂.geomMorph P = L then 1 else 0))
        - ((if D₁.geomMorph P + D₂.geomMorph P = 0 then 1 else 0)
          - (if D₁.geomMorph P = 0 then 1 else 0)
          - (if D₂.geomMorph P = 0 then 1 else 0)) := by
  have h1 := kw_dcao_unramified_proved D₁
  have h2 := kw_dcao_unramified_proved D₂
  have h3 := kw_dcao_unramified_proved D₃
  have hL := kw_dcao_defect_pullback_placeOfPoint_apply_of_unramified D₁ D₂ D₃ h1 h2 h3 L P
  have h0 := kw_dcao_defect_pullback_placeOfPoint_apply_of_unramified D₁ D₂ D₃ h1 h2 h3 0 P
  rw [hgm P] at hL h0
  simp only [coe_pointDivisor, map_sub, ← sub_sub, Finsupp.sub_apply] at *
  linear_combination hL - h0

theorem kw_dcao_defectPrincipalPerPoint_of_specLineOrdMatchHgm
    (hSLO : KwDCAOSpecLineOrdMatchHgm W) :
    KwDCAODefectPrincipalPerPoint W := by
  intro D₁ D₂ D₃ hgm hX L
  rcases L with _ | ⟨a, b, h⟩
  · have h0 : (pointDivisor (0 : W.Point) : Divisor F W.FunctionField) = 0 := by
      rw [coe_pointDivisor, sub_self]
    change Divisor.IsPrincipal _
    rw [show (Point.zero : W.Point) = 0 from rfl,
      h0, _root_.map_zero, _root_.map_zero, _root_.map_zero, zero_add, sub_zero]
    exact Divisor.principal.zero_mem
  · have hVne := kw_dcao_specVert_ne_zero_of_hgm D₁ D₂ D₃ hgm a
    obtain ⟨hLne, hLord⟩ := hSLO D₁ D₂ D₃ hgm hX h
    have hne : kw_dcao_specExplicit D₁ D₂ a b ≠ 0 :=
      mul_ne_zero hVne (inv_ne_zero hLne)
    refine ⟨kw_dcao_specExplicit D₁ D₂ a b, hne, fun v => ?_⟩
    set P := (placeOfPointEquiv W).symm v with hP
    have hv : v = placeOfPoint P := (placeOfPoint_placeOfPointEquiv_symm W v).symm
    have hcoeff := kw_dcao_defect_pointDivisor_coeff D₁ D₂ D₃ hgm (Point.some a b h) P
    rw [hv, hcoeff,
      show kw_dcao_specExplicit D₁ D₂ a b
        = kw_dcao_specVert D₁ D₂ a * (kw_dcao_specLine D₁ D₂ a b)⁻¹ from rfl,
      (placeOfPoint P).ord_mul hVne (inv_ne_zero hLne), (placeOfPoint P).ord_inv,
      kw_dcao_ord_specVert_eq_transport D₁ D₂ D₃ hgm hX a P, hLord P]
    ring

theorem kw_dcao_htw_of_specLineOrdMatchHgm (hSLO : KwDCAOSpecLineOrdMatchHgm W) :
    KwDualTraceWitness W :=
  kw_dcao_htw_of_defectPrincipal
    (kw_dcao_defectPrincipalPerPoint_of_specLineOrdMatchHgm hSLO)

theorem kw_dcao_htw_of_allAffine (hAA : KwDCAOSpecLineOrdMatchAllAffine W) :
    KwDualTraceWitness W :=
  kw_dcao_htw_of_specLineOrdMatchHgm
    (kw_dcao_specLineOrdMatch_hgm_of_allAffine hAA)

end GeneralW
end Affine
end WeierstrassCurve
end
end

section

section

namespace WeierstrassCurve
namespace Affine
universe u

section GeneralW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

theorem kw_dcao_htw_proved : KwDualTraceWitness W :=
  kw_dcao_htw_of_allAffine kw_dcao_specLineOrdMatch_allAffine_proved

end GeneralW
end Affine
end WeierstrassCurve
end
end

open WeierstrassCurve WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine
  AlgebraicCurve in
universe u in
theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin) (D : IsogenyEndDatum W) :
    ∃ DD : AddMonoid.End.DualEndData (D.pointEnd (hNs D)),
      DD.dual ∈ isogenyEndSubring W hNs ∧ DD.norm = finrankAlong F D.ι := by
  have htw : KwDualTraceWitness W := kw_dcao_htw_proved
  have hfun : hNs = fun D => D.normFormulaAlong_auto := rfl
  subst hfun
  exact ⟨kw_dualEndData_of_traceWitness htw D, kw_dualInSubring_of_traceWitness htw D, rfl⟩

end
end
end
end

end privateSection

public section publicSection

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin) (D : IsogenyEndDatum W) :
    ∃ DD : AddMonoid.End.DualEndData (D.pointEnd (hNs D)),
      DD.dual ∈ isogenyEndSubring W hNs ∧ DD.norm = finrankAlong F D.ι := _root_.solution hNs D

end publicSection
