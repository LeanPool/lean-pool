/-
Based on Prove2Me node
WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int
(012791e6-9417-5e9d-b060-7ab6c0060cd8) by Claude (2026-09-05).

Proof based on Prove2Me submission 4d7ded92-6949-5c83-832a-9fae9dc5d7cf
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Mathlib.RingTheory.HahnSeries.Summable
public import LeanPool.FLTEichlerShimura.Definitions.Def_Isogeny_ConditionalCurrency
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_OddOrderSummingSet
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_Velu

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.Data.Int.Star
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_finiteAlong_of_surjective
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_normFormulaAlong
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_isCentred
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Equal j of Vélu quotients forces equal cyclic subgroups

Theorem statement:
`WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int`
(`012791e6-9417-5e9d-b060-7ab6c0060cd8`), by Claude, 2026-09-05.

Proof: submission `4d7ded92-6949-5c83-832a-9fae9dc5d7cf`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $\mathbb{K}=\mathrm{HahnSeries}\,\mathbb{Q}\,\overline{\mathbb{Q}}$ be the field of Hahn series
with rational exponents and coefficients in an algebraic closure of $\mathbb{Q}$, assumed
algebraically closed of characteristic $0$, and let $W$ be an elliptic Weierstrass curve over
$\mathbb{K}$. Assume for its affine model: a `GenusOnePlaceGate`, i.e. a bijection between $W$'s
affine point group and the places of its function field over $\mathbb{K}$, all of degree $1$; that
this gate is centred, i.e. for each nonsingular $(x,y)$ the classes of the coordinate functions $X$
and $Y-y$ lie in the nonunits of the valuation subring at the corresponding place; and
`AbelTheorem`, i.e. a degree-zero divisor is principal exactly when its divisor sum vanishes. Assume
further that for every isogeny endomorphism datum $D$ of $W$ (an integral $\mathbb{K}$-algebra
endomorphism $\iota$ of the function field along which the field is module-finite over itself) the
pushforward norm formula holds along $D.\iota$, and that the induced endomorphism
$D.\mathrm{pointEnd}$ of the point group is multiplication by some integer $m$. Let $n\in\mathbb{N}$
and let $Q,Q'$ both have additive order $2n+1$. Suppose the Vélu quotient curves formed from the
summing sets $\{(k\cdot Q)\text{-coordinates}:1\le k\le n\}$, resp. for $Q'$, have nonzero
discriminant, hence are elliptic, and have equal $j$-invariants. Then the subgroups of integer
multiples of $Q$ and of $Q'$ coincide.

This is the injectivity-on-cyclic-subgroups statement for $j$ of Vélu quotients for a curve whose
endomorphisms are all integer multiples (Silverman, AEC III.4.12 in the form
$\operatorname{Hom}(E,E')\cong\mathbb{Z}$): distinct cyclic subgroups of the same odd order give
quotients with distinct $j$-invariants. It feeds the companion statement
[`WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental`]
(thm.html#WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental),
where the hypotheses on endomorphisms are replaced by transcendence of the parameter.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int.lean

<!-- Generated by add_prove2me_provenance.py -->
-/


section privateSection

set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_OVERLONG_9421e021

set_option linter.unusedVariables false

noncomputable section

namespace ModularCurve

theorem cmm5_dp_natCard_ker_comp {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (AddMonoidHom.ker (g.comp f))
      = Nat.card (AddMonoidHom.ker g) * Nat.card (AddMonoidHom.ker f) := by
  have hmem : ∀ x : AddMonoidHom.ker (g.comp f),
      (f.domRestrict (AddMonoidHom.ker (g.comp f))) x ∈ AddMonoidHom.ker g := by
    intro x
    have hx := x.2
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_ker]
    exact hx
  have hle : AddMonoidHom.ker f ≤ AddMonoidHom.ker (g.comp f) := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hx, map_zero]
  have hφker : Nat.card (AddMonoidHom.ker
        (AddMonoidHom.codRestrict (f.domRestrict (AddMonoidHom.ker (g.comp f)))
          (AddMonoidHom.ker g) hmem))
      = Nat.card (AddMonoidHom.ker f) := by
    rw [AddMonoidHom.ker_codRestrict, AddMonoidHom.ker_domRestrict]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv
  have hφsurj : Function.Surjective
      (AddMonoidHom.codRestrict (f.domRestrict (AddMonoidHom.ker (g.comp f)))
        (AddMonoidHom.ker g) hmem) := by
    intro y
    have hy : g (y : B) = 0 := by
      have h := y.2
      rwa [AddMonoidHom.mem_ker] at h
    obtain ⟨x, hx⟩ := hf (y : B)
    have hxK : x ∈ AddMonoidHom.ker (g.comp f) := by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hx]
      exact hy
    exact ⟨⟨x, hxK⟩, Subtype.ext hx⟩
  calc Nat.card (AddMonoidHom.ker (g.comp f))
      = Nat.card (AddMonoidHom.ker (g.comp f) ⧸ AddMonoidHom.ker
            (AddMonoidHom.codRestrict (f.domRestrict (AddMonoidHom.ker (g.comp f)))
              (AddMonoidHom.ker g) hmem))
          * Nat.card (AddMonoidHom.ker
            (AddMonoidHom.codRestrict (f.domRestrict (AddMonoidHom.ker (g.comp f)))
              (AddMonoidHom.ker g) hmem)) :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card (AddMonoidHom.ker g) * Nat.card (AddMonoidHom.ker f) := by
        rw [Nat.card_congr
          (QuotientAddGroup.quotientKerEquivOfSurjective _ hφsurj).toEquiv, hφker]

end ModularCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map exists_variableChange_of_j_eq IsIntegral toAffine \
  Affine.Point Δ j veluQuotient oddOrderSummingSet \
  exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples \
  Affine.Point.exists_zsmul_eq_of_isAlgClosed card_torsionBy_eq_sq_of_isAlgClosed \
  nonempty_functionField_algEquiv_of_variableChange"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "CoordinateRing map FunctionField Point pointMapOfPushforward \
  pointMapOfPushforward_apply IsogenyEndDatum IsogenyHomDatum IsogenyHomDatum.ofEndDatum \
  GenusOnePlaceGate pointClass AbelTheorem genusOnePic0Equiv genusOnePic0Equiv_symm_apply \
  GenusOnePlaceGate.IsCentred IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred \
  natCard_ker_pointMapOfPushforward_eq_finrankAlong pointMapOfPushforward_surjective \
  Point.exists_zsmul_eq_of_isAlgClosed IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring \
  exists_genusOnePlaceGate_isCentred_and_abelTheorem CoordinateRing.isDedekindDomain \
  hasPrincipalDivisors_functionField"
p2m_open "WeierstrassCurve.Affine~pointHom WeierstrassCurve"

open AlgebraicCurve

scoped instance instHasPrincipalDivisorsFunctionField_s13jb {F : Type*} [Field F] [CharZero F]
    {W : Affine F} : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField W

section AutoNorm

variable {F : Type*} [Field F] [CharZero F] {V W : Affine F}

theorem normFormulaAlong_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hfin : FiniteAlong F ι) : NormFormulaAlong F ι hfin := by
  classical
  have : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  have hsep : SeparableAlong F ι := by
    let := algebraAlong ι
    have := isScalarTower_along ι
    have : Module.Finite V.FunctionField W.FunctionField := hfin
    change Algebra.IsSeparable V.FunctionField W.FunctionField
    infer_instance
  exact AlgebraicCurve.normFormulaAlong ι hfin hsep

end AutoNorm

section Torsion

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic]

theorem charZero_addMonoidEnd_point : CharZero (AddMonoid.End W.Point) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  have htop : ∀ k : ℕ, n ∣ k → Submodule.torsionBy ℤ W.Point (k : ℤ) = ⊤ := by
    rintro k ⟨c, rfl⟩
    refine eq_top_iff.mpr fun P _ => ?_
    rw [Submodule.mem_torsionBy_iff]
    have hP : (n : ℤ) • P = 0 := by
      have h := DFunLike.congr_fun hn P
      rw [AddMonoid.End.natCast_apply] at h
      rw [natCast_zsmul]; exact h
    rw [Nat.cast_mul, mul_comm, mul_smul, hP, smul_zero]
  have hcard : ∀ k : ℕ, n ∣ k → k ≠ 0 → Nat.card W.Point = k ^ 2 := by
    intro k hk hk0
    have h : Nat.card (Submodule.torsionBy ℤ W.Point (k : ℤ)) = k ^ 2 :=
      WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := k)
        (Nat.cast_ne_zero.mpr hk0)
    rw [htop k hk] at h
    rwa [Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := W.Point)).toEquiv] at h
  have h1 := hcard n dvd_rfl hn0
  have h2 := hcard (2 * n) (dvd_mul_left n 2) (by omega)
  have h3 : n ^ 2 = (2 * n) ^ 2 := h1.symm.trans h2
  have h4 : 3 * n ^ 2 = 0 := by nlinarith
  have h5 : n = 0 := by
    have : n ^ 2 = 0 := by omega
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact hn0 h5

theorem intCast_addMonoidEnd_point_injective :
    Function.Injective (Int.cast : ℤ → AddMonoid.End W.Point) :=
  haveI := charZero_addMonoidEnd_point W
  Int.cast_injective

variable {W} in
omit [DecidableEq F] in
theorem kw_point_infinite : Infinite W.Point := by
  classical
  rw [← not_finite_iff_infinite]
  intro hfinite
  have : Finite W.Point := hfinite
  set N : ℕ := Nat.card W.Point with hN
  have hNpos : 0 < N := Nat.card_pos
  have htop : ∀ k : ℕ, N ∣ k → Submodule.torsionBy ℤ W.Point (k : ℤ) = ⊤ := by
    rintro k ⟨c, rfl⟩
    refine eq_top_iff.mpr fun P _ => ?_
    rw [Submodule.mem_torsionBy_iff]
    have hP : (N : ℤ) • P = 0 := by
      rw [natCast_zsmul, hN]; exact card_nsmul_eq_zero'
    rw [Nat.cast_mul, mul_comm, mul_smul, hP, smul_zero]
  have hcard : ∀ k : ℕ, N ∣ k → k ≠ 0 → N = k ^ 2 := by
    intro k hk hk0
    have h : Nat.card (Submodule.torsionBy ℤ W.Point (k : ℤ)) = k ^ 2 :=
      WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := k)
        (Nat.cast_ne_zero.mpr hk0)
    rw [htop k hk] at h
    rwa [Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := W.Point)).toEquiv, ← hN] at h
  have h1 := hcard N dvd_rfl hNpos.ne'
  have h2 := hcard (2 * N) (dvd_mul_left N 2) (by omega)
  have h3 : N ^ 2 = (2 * N) ^ 2 := h1.symm.trans h2
  have h4 : N ^ 2 = 0 := by nlinarith
  exact hNpos.ne' (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4)

variable {W} in
theorem kw_nat_card_ker_of_zsmul {f : W.Point →+ W.Point} {N : ℤ}
    (hN : N ≠ 0) (hf : ∀ P, f P = N • P) : Nat.card f.ker = N.natAbs ^ 2 := by
  have hsets : ∀ P : W.Point,
      P ∈ f.ker ↔ P ∈ Submodule.torsionBy ℤ W.Point (N.natAbs : ℤ) := by
    intro P
    rw [AddMonoidHom.mem_ker, hf, Submodule.mem_torsionBy_iff]
    constructor
    · intro hP
      rcases Int.natAbs_eq N with h | h
      · rwa [h] at hP
      · rwa [h, neg_zsmul, neg_eq_zero] at hP
    · intro hP
      rcases Int.natAbs_eq N with h | h
      · rw [h]; exact hP
      · rw [h, neg_zsmul, neg_eq_zero]; exact hP
  rw [Nat.card_congr (Equiv.subtypeEquivRight hsets)]
  exact WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := N.natAbs)
    (Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN))

variable {W} in
omit [CharZero F] in
theorem kw_eq_zero_of_zsmul_eq_zero {N : ℤ} (hN : N ≠ 0) {G : Type*} [AddCommGroup G]
    (δ : W.Point →+ G) (hδ : ∀ P, N • δ P = 0) : δ = 0 := by
  refine AddMonoidHom.ext fun P => ?_
  obtain ⟨R, hR⟩ : ∃ R : W.Point, N • R = P :=
    WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed W hN P
  rw [← hR, map_zsmul]; exact hδ R

end Torsion

section Functoriality

universe u

variable {F : Type u} [Field F] [DecidableEq F]
variable {A B C : Affine F}
  [GenusOnePlaceGate A] [AbelTheorem A]
  [GenusOnePlaceGate B] [AbelTheorem B]
  [GenusOnePlaceGate C] [AbelTheorem C]

omit [DecidableEq F] [A.GenusOnePlaceGate] [A.AbelTheorem] [B.GenusOnePlaceGate]
  [B.AbelTheorem] [C.GenusOnePlaceGate] [C.AbelTheorem] in
theorem Pic0_pushforwardAlongHom_comp
    (f : B.FunctionField →ₐ[F] A.FunctionField) (hf : f.toRingHom.IsIntegral)
    (hfinf : FiniteAlong F f) (hNf : NormFormulaAlong F f hfinf)
    (g : C.FunctionField →ₐ[F] B.FunctionField) (hg : g.toRingHom.IsIntegral)
    (hfing : FiniteAlong F g) (hNg : NormFormulaAlong F g hfing)
    (hfg : (f.comp g).toRingHom.IsIntegral) (hfinfg : FiniteAlong F (f.comp g))
    (hNfg : NormFormulaAlong F (f.comp g) hfinfg)
    (x : Pic0 F A.FunctionField) :
    Pic0.pushforwardAlongHom g hg hfing hNg (Pic0.pushforwardAlongHom f hf hfinf hNf x)
      = Pic0.pushforwardAlongHom (f.comp g) hfg hfinfg hNfg x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk]
  congr 1
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pushforwardAlongDegZero,
    Pic0.coe_pushforwardAlongDegZero]
  exact Divisor.pushforwardAlong_pushforwardAlong g f hg hf hfg (D : Divisor F A.FunctionField)

theorem pointMapOfPushforward_comp
    (f : B.FunctionField →ₐ[F] A.FunctionField) (hf : f.toRingHom.IsIntegral)
    (hfinf : FiniteAlong F f) (hNf : NormFormulaAlong F f hfinf)
    (g : C.FunctionField →ₐ[F] B.FunctionField) (hg : g.toRingHom.IsIntegral)
    (hfing : FiniteAlong F g) (hNg : NormFormulaAlong F g hfing)
    (hfg : (f.comp g).toRingHom.IsIntegral) (hfinfg : FiniteAlong F (f.comp g))
    (hNfg : NormFormulaAlong F (f.comp g) hfinfg) (P : A.Point) :
    pointMapOfPushforward (f.comp g) hfg hfinfg hNfg P
      = pointMapOfPushforward g hg hfing hNg (pointMapOfPushforward f hf hfinf hNf P) := by
  have key : ∀ x : Pic0 F B.FunctionField, pointClass (genusOnePic0Equiv B x) = x := fun x => by
    rw [← genusOnePic0Equiv_symm_apply, AddEquiv.symm_apply_apply]
  rw [pointMapOfPushforward_apply, pointMapOfPushforward_apply, pointMapOfPushforward_apply, key,
    Pic0_pushforwardAlongHom_comp f hf hfinf hNf g hg hfing hNg hfg hfinfg hNfg]

end Functoriality

section IsoInjective

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {A B : Affine F}
  [A.IsElliptic] [GenusOnePlaceGate A] [AbelTheorem A]
  [B.IsElliptic] [GenusOnePlaceGate B] [AbelTheorem B]

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic A]
  [A.GenusOnePlaceGate] [A.AbelTheorem] [WeierstrassCurve.IsElliptic B] [B.GenusOnePlaceGate]
  [B.AbelTheorem] in
theorem finrankAlong_eq_one_of_bijective (τ : B.FunctionField →ₐ[F] A.FunctionField)
    (hτ : Function.Bijective τ) : finrankAlong F τ = 1 := by
  let := algebraAlong τ
  let σ : B.FunctionField ≃+* A.FunctionField := RingEquiv.ofBijective τ hτ
  let e : A.FunctionField ≃ₗ[B.FunctionField] B.FunctionField :=
    { σ.symm.toAddEquiv with
      map_smul' := fun b x => by
        change σ.symm (b • x) = b * σ.symm x
        rw [Algebra.smul_def, map_mul]
        congr 1
        exact σ.symm_apply_apply b }
  change Module.finrank B.FunctionField A.FunctionField = 1
  rw [e.finrank_eq, Module.finrank_self]

theorem pointMapOfPushforward_injective_of_bijective
    (τ : B.FunctionField →ₐ[F] A.FunctionField) (hτ : τ.toRingHom.IsIntegral)
    (hfin : FiniteAlong F τ) (hN : NormFormulaAlong F τ hfin) (hbij : Function.Bijective τ) :
    Function.Injective (pointMapOfPushforward τ hτ hfin hN) := by
  have hcard : Nat.card (pointMapOfPushforward τ hτ hfin hN).ker = 1 := by
    rw [natCard_ker_pointMapOfPushforward_eq_finrankAlong A B τ hτ hfin hN,
      finrankAlong_eq_one_of_bijective τ hbij]
  have : Finite (pointMapOfPushforward τ hτ hfin hN).ker :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact one_ne_zero)
  have hbot : (pointMapOfPushforward τ hτ hfin hN).ker = ⊥ :=
    AddSubgroup.eq_bot_of_card_eq _ hcard
  exact (AddMonoidHom.ker_eq_bot_iff _).mp hbot

end IsoInjective

end WeierstrassCurve.Affine

namespace ModularCurve

p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_9421e021.W\
  eierstrassCurve WeierstrassCurve.Affine~pointHom \
  P2MW.S_OVERLONG_9421e021.W\
  eierstrassCurve.Affine AlgebraicCurve"

universe u

attribute [local instance] Classical.propDecidable

theorem kw_veluOddQuotientJInjOnCyclic_of_isogenyEndInt
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
    [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong F D.ι D.hfin)
    (hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ P : W.toAffine.Point,
      D.pointEnd (hNs D) P = m • P)
    (n : ℕ) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) (hQ' : addOrderOf Q' = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q' n)).Δ ≠ 0)
    (hj : haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic :=
        ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.veluQuotient (W.oddOrderSummingSet Q' n)).IsElliptic :=
        ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j
        = (W.veluQuotient (W.oddOrderSummingSet Q' n)).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' := by
  classical
  have hell : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hell' : (W.veluQuotient (W.oddOrderSummingSet Q' n)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
  have : IsDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q n))
  have : IsDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q' n)).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q' n))
  obtain ⟨gV, hcV, haV⟩ := exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine)
  obtain ⟨gV', hcV', haV'⟩ := exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (W.veluQuotient (W.oddOrderSummingSet Q' n)).toAffine)
  let := gV
  let := gV'
  have := hcV
  have := hcV'
  have := haV
  have := haV'
  obtain ⟨ι, hι, hfin, -, hkerQ⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples hQ hΔ
  obtain ⟨ι', hι', hfin', -, hkerQ'⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples hQ' hΔ'
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (W.veluQuotient (W.oddOrderSummingSet Q n))
    (W.veluQuotient (W.oddOrderSummingSet Q' n)) hj
  obtain ⟨σ⟩ : Nonempty ((W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
      ≃ₐ[F] (W.veluQuotient (W.oddOrderSummingSet Q' n)).toAffine.FunctionField) :=
    hC ▸ WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange
      (W.veluQuotient (W.oddOrderSummingSet Q n)) C
  set τ : (W.veluQuotient (W.oddOrderSummingSet Q' n)).toAffine.FunctionField
      →ₐ[F] (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField :=
    σ.symm.toAlgHom with hτ_def
  have hτbij : Function.Bijective τ := σ.symm.bijective
  have hτint : τ.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ hτbij.2
  have hτfin : FiniteAlong F τ := finiteAlong_of_surjective τ hτbij.2
  have hNτ : NormFormulaAlong F τ hτfin := normFormulaAlong_of_elliptic τ hτfin
  have hNι : NormFormulaAlong F ι hfin := normFormulaAlong_of_elliptic ι hfin
  have hNι' : NormFormulaAlong F ι' hfin' := normFormulaAlong_of_elliptic ι' hfin'
  have hιτint : (ι.comp τ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hτint hι
  have hιτfin : FiniteAlong F (ι.comp τ) := finiteAlong_comp τ ι hτfin hfin
  have hNιτ : NormFormulaAlong F (ι.comp τ) hιτfin := normFormulaAlong_of_elliptic _ hιτfin
  set φ := pointMapOfPushforward ι hι hfin hNι with hφ_def
  set φ' := pointMapOfPushforward ι' hι' hfin' hNι' with hφ'_def
  set β := pointMapOfPushforward (ι.comp τ) hιτint hιτfin hNιτ with hβ_def
  have hβ_comp : ∀ P, β P = pointMapOfPushforward τ hτint hτfin hNτ (φ P) := fun P =>
    pointMapOfPushforward_comp ι hι hfin hNι τ hτint hτfin hNτ hιτint hιτfin hNιτ P
  have hτinj := pointMapOfPushforward_injective_of_bijective τ hτint hτfin hNτ hτbij
  have hkerφ : φ.ker = AddSubgroup.zmultiples Q := hkerQ hNι
  have hkerφ' : φ'.ker = AddSubgroup.zmultiples Q' := hkerQ' hNι'
  have hkerβ : β.ker = AddSubgroup.zmultiples Q := by
    rw [← hkerφ]
    refine AddSubgroup.ext fun P => ?_
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hβ_comp]
    refine ⟨fun h => hτinj (h.trans (map_zero _).symm), fun h => ?_⟩
    rw [h, map_zero]
  have hβs : Function.Surjective β :=
    pointMapOfPushforward_surjective W.toAffine _ (ι.comp τ) hιτint hιτfin hNιτ
  have hφ's : Function.Surjective φ' :=
    pointMapOfPushforward_surjective W.toAffine _ ι' hι' hfin' hNι'
  have hNne : ((2 * n + 1 : ℤ) : AddMonoid.End W.toAffine.Point) ≠ 0 := by
    intro h
    have := intCast_addMonoidEnd_point_injective W.toAffine (h.trans Int.cast_zero.symm)
    omega
  obtain ⟨M, hM⟩ := IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring hNs
    ((2 * n + 1 : ℤ) : AddMonoid.End W.toAffine.Point) (intCast_mem _ _) hNne
  have hMapp : ∀ P, M.pointEnd (hNs M) P = (2 * n + 1 : ℤ) • P := fun P => by
    rw [hM, AddMonoid.End.intCast_apply]
  let φ'D : IsogenyHomDatum W.toAffine (W.veluQuotient (W.oddOrderSummingSet Q' n)).toAffine :=
    ⟨ι', hι', hfin'⟩
  have hmem_of_ker : ∀ P, φ' P = 0 → (2 * n + 1 : ℤ) • P = 0 := by
    intro P hP
    have hPm : P ∈ AddSubgroup.zmultiples Q' := by rw [← hkerφ']; exact hP
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hPm
    have h21 : (2 * n + 1 : ℤ) • Q' = 0 := by
      have h : ((2 * n + 1 : ℕ) : ℤ) • Q' = 0 := by
        rw [natCast_zsmul, ← hQ', addOrderOf_nsmul_eq_zero]
      exact_mod_cast h
    rw [smul_comm, h21, zsmul_zero]
  obtain ⟨χ, hNχ, hχ⟩ := IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred φ'D hNι'
    (IsogenyHomDatum.ofEndDatum M) (hNs M) (fun P hP => by
      change M.pointEnd (hNs M) P = 0
      rw [hMapp]; exact hmem_of_ker P hP)
  set ψ' := χ.pointHom hNχ with hψ'_def
  have hdual₁ : ∀ P, ψ' (φ' P) = (2 * n + 1 : ℤ) • P := fun P => by
    have h := hχ P
    rw [← hMapp P]; exact h
  have hdual₂ : ∀ S, φ' (ψ' S) = (2 * n + 1 : ℤ) • S := fun S => by
    obtain ⟨P, rfl⟩ := hφ's S
    rw [hdual₁, map_zsmul]
  have hDint : ((ι.comp τ).comp χ.ι).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ χ.hι hιτint
  let D : IsogenyEndDatum W.toAffine :=
    ⟨(ι.comp τ).comp χ.ι, hDint, finiteAlong_comp χ.ι (ι.comp τ) χ.hfin hιτfin⟩
  have hD : ∀ P, D.pointEnd (hNs D) P = ψ' (β P) := fun P =>
    pointMapOfPushforward_comp (ι.comp τ) hιτint hιτfin hNιτ χ.ι χ.hι χ.hfin hNχ
      hDint D.hfin (hNs D) P
  obtain ⟨m, hm⟩ := hEnd D
  set θ := ψ'.comp β with hθ_def
  have hθm : ∀ P, θ P = m • P := fun P => by
    change ψ' (β P) = m • P
    rw [← hD P]; exact hm P
  have hcardQ' : Nat.card (AddSubgroup.zmultiples Q') = 2 * n + 1 := by
    rw [Nat.card_zmultiples, hQ']
  have hcardQ : Nat.card (AddSubgroup.zmultiples Q) = 2 * n + 1 := by
    rw [Nat.card_zmultiples, hQ]
  have hkerψ' : Nat.card ψ'.ker = 2 * n + 1 := by
    have hcomp : Nat.card (ψ'.comp φ').ker = (2 * n + 1) ^ 2 := by
      have h := kw_nat_card_ker_of_zsmul (W := W.toAffine) (f := ψ'.comp φ')
        (N := (2 * n + 1 : ℤ)) (by omega) (fun P => hdual₁ P)
      have habs : (2 * (n : ℤ) + 1).natAbs = 2 * n + 1 := by omega
      rw [habs] at h; exact h
    have hsplit := cmm5_dp_natCard_ker_comp φ' ψ' hφ's
    rw [hcomp, hkerφ', hcardQ', sq] at hsplit
    exact (Nat.eq_of_mul_eq_mul_right (by omega) hsplit).symm
  have hkerθ : Nat.card θ.ker = (2 * n + 1) ^ 2 := by
    have hsplit := cmm5_dp_natCard_ker_comp β ψ' hβs
    rw [hkerβ, hcardQ, hkerψ'] at hsplit
    rw [hsplit]; ring
  have hmne : m ≠ 0 := by
    intro h0
    have hall : ∀ P, θ P = 0 := fun P => by rw [hθm, h0, zero_zsmul]
    have htop : θ.ker = ⊤ :=
      AddSubgroup.ext fun P => ⟨fun _ => trivial, fun _ => AddMonoidHom.mem_ker.mpr (hall P)⟩
    rw [htop] at hkerθ
    have : Infinite W.toAffine.Point := kw_point_infinite
    simp only [AddSubgroup.card_top, Nat.card_eq_zero_of_infinite] at hkerθ
    exact absurd hkerθ.symm (by positivity)
  have hm_abs : m.natAbs = 2 * n + 1 := by
    have hcard := kw_nat_card_ker_of_zsmul (W := W.toAffine) hmne hθm
    rw [hkerθ, sq, sq] at hcard
    exact (Nat.mul_self_inj).mp hcard.symm
  have hkey : ∀ P, (2 * n + 1 : ℤ) • β P = m • φ' P := fun P => by
    have h1 : φ' (ψ' (β P)) = (2 * n + 1 : ℤ) • β P := hdual₂ (β P)
    have h2 : φ' (θ P) = m • φ' P := by rw [hθm, map_zsmul]
    rw [← h1]; exact h2
  have hmcases : m = (2 * n + 1 : ℤ) ∨ m = -(2 * n + 1 : ℤ) := by
    rcases Int.natAbs_eq m with h | h <;> [left; right] <;> omega
  have hNz : (2 * n + 1 : ℤ) ≠ 0 := by omega
  have hkerβ' : β.ker = AddSubgroup.zmultiples Q' := by
    rcases hmcases with hm' | hm'
    · have hδ : β - φ' = 0 :=
        kw_eq_zero_of_zsmul_eq_zero (W := W.toAffine) hNz (β - φ') fun P => by
          rw [AddMonoidHom.sub_apply, smul_sub, hkey P, hm', sub_self]
      have heq : β = φ' := sub_eq_zero.mp hδ
      rw [heq]; exact hkerφ'
    · have hδ : β + φ' = 0 :=
        kw_eq_zero_of_zsmul_eq_zero (W := W.toAffine) hNz (β + φ') fun P => by
          rw [AddMonoidHom.add_apply, smul_add, hkey P, hm', ← add_smul, neg_add_cancel,
            zero_smul]
      have heq : β = -φ' := eq_neg_iff_add_eq_zero.mpr hδ
      rw [heq, ← hkerφ']
      exact AddSubgroup.ext fun P => by
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.neg_apply, neg_eq_zero]
  exact hkerβ.symm.trans hkerβ'

end ModularCurve
end

p2m_open "WeierstrassCurve.Affine~pointHom\
  " in
open _root_.WeierstrassCurve
  _root_.P2MW.S_OVERLONG_9421e021.WeierstrassCurve
  _root_.P2MW.S_OVERLONG_9421e021.WeierstrassCurve.Affine
  AlgebraicCurve in
theorem solution
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))] [CharZero (HahnSeries ℚ (AlgebraicClosure ℚ))]
    [IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong (HahnSeries ℚ (AlgebraicClosure ℚ))
      D.ι D.hfin)
    (hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P
      = m • P)
    (n : ℕ) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) (hQ' : addOrderOf Q' = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q' n)).Δ ≠ 0)
    (hj : haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr
      hΔ⟩
      haveI : (W.veluQuotient (W.oddOrderSummingSet Q' n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr
        hΔ'⟩
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j = (W.veluQuotient (W.oddOrderSummingSet Q'
        n)).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' :=
  ModularCurve.kw_veluOddQuotientJInjOnCyclic_of_isogenyEndInt W hNs hEnd n Q Q' hQ hQ' hΔ hΔ' hj

end S_OVERLONG_9421e021
end P2MW
export
  P2MW.S_OVERLONG_9421e021
  (solution)

end privateSection

public section publicSection


open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
theorem WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))] [CharZero (HahnSeries ℚ (AlgebraicClosure ℚ))]
    [IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong (HahnSeries ℚ (AlgebraicClosure ℚ))
      D.ι D.hfin)
    (hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P
      = m • P)
    (n : ℕ) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) (hQ' : addOrderOf Q' = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q' n)).Δ ≠ 0)
    (hj : haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr
      hΔ⟩
      haveI : (W.veluQuotient (W.oddOrderSummingSet Q' n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr
        hΔ'⟩
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j = (W.veluQuotient (W.oddOrderSummingSet Q'
        n)).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' :=
  solution W hNs hEnd n Q Q' hQ hQ' hΔ hΔ' hj

end publicSection
