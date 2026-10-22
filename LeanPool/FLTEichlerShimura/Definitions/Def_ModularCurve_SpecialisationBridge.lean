/-
Based on Prove2Me node ModularCurve_SpecialisationBridge
(52ff15a8-6143-55a5-8df2-6a5dc3d7422f) by Claude (2026-09-05).

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_SpecialisationVocab
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_TatePoint
public import LeanPool.FLTEichlerShimura.Definitions.Def_HahnSeries_Monodromy
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
public import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_goodModel_zero_spec
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_goodModel_1728_spec
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_goodModel_generic_spec
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_nearCurve_eq_ofJNe0Or1728
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_exists_variableChange_specialFibre_goodModel
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_isElliptic_specialFibre_goodModel
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_isElliptic_specialFibre
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_exists_torsionBy_reduction_addEquiv

/-!
# Reduction of points and specialisation of cyclic p-subgroups

Definition: `ModularCurve_SpecialisationBridge` (`52ff15a8-6143-55a5-8df2-6a5dc3d7422f`), by Claude,
2026-09-05.

Throughout, $\bar{\mathbb Q}$ is an algebraic closure of $\mathbb Q$ and $H = \mathrm{HahnSeries}\
\mathbb Q\ \bar{\mathbb Q}$ is the field of Hahn series with rational exponents; a Weierstrass curve
$W$ over $H$ has `IntegralCoeffs` when each $a_i$ has non-negative `orderTop`, and `specialFibre W`
is the Weierstrass curve over $\bar{\mathbb Q}$ whose coefficients are the degree-$0$ coefficients
of the $a_i$. The first group of declarations is the coefficientwise reduction: if $x,y$ have
non-negative order and $(x,y)$ satisfies (resp. is a nonsingular point of) the affine equation of
$W$, then $(x_0,y_0)$ satisfies (resp. is nonsingular on) `specialFibre W`, the nonsingularity
statement using that the special fibre is elliptic when $\Delta_W$ has order exactly $0$. The
function `redPoint` sends the point at infinity to $0$, a point with both coordinates of
non-negative order to its reduction, and every other affine point to $0$; it is defined as a
function on points, no additivity being asserted.

The second group manipulates the type `CycOf A N` of subgroups of an additive group $A$ of the form
$\mathbb Z g$ with $g$ of additive order exactly $N$; the project's types `CycSubH E N` and `CycSub
E₀ N` of cyclic $N$-subgroups of points are recorded as this type. Bijections of this type are
produced from an additive equivalence (`cycOfCongr`, by pushing subgroups forward), and from the
inclusion of the $N$-torsion submodule (`cycOfTorsionBy`, by pulling back along $\mathrm{torsionBy}\
\mathbb Z\ A\ N \hookrightarrow A$), with small helpers on torsion membership and on comap of
$\mathbb Z g$. Additive equivalences of point groups are supplied by `vcAddEquiv` (the inverse of
the point bijection attached to a variable change, additive by `vcInvFun_add`) and by
`pointAddEquivOfEq` (transport along an equality of curves).

At a $j$-value $j_0 \in \bar{\mathbb Q}$, `nearCurve j₀` is the curve of invariant $j_0 + q$ and
`goodModel j₀` is its twist by the variable change `scaleVC j₀` (a rescaling by a fractional power
of $q$ when $j_0 = 0$ or $1728$, the identity otherwise); `goodModel_spec` records that this model
has integral coefficients and discriminant of order $0$. `fibreVC` is a chosen variable change
carrying `specialFibre (goodModel j₀)` to `ofJ j₀`, and `fibreAddEquiv` the resulting additive
equivalence of point groups; `scaleAddEquiv` is the point equivalence between `nearCurve j₀` and
`goodModel j₀`, and `cycScale` its effect on cyclic $p$-subgroups. `redTorsionEquiv` is a chosen
additive equivalence between the $p$-torsion of $W$ and that of `specialFibre W`, characterised by
`redTorsionEquiv_spec`: it acts on an affine $p$-torsion point $(x,y)$ by $(x_0,y_0)$. Composing
gives `cycRed`, a bijection from cyclic $p$-subgroups of $W$ to those of `specialFibre W`, and
`bridge3Specialise`, a bijection from cyclic $p$-subgroups of `nearCurve j₀` to those of `ofJ j₀`,
for $p$ prime.

The last group is the monodromy action. A ring endomorphism of $H$ fixing the constants $C(q)$ and
the element $q = \mathrm{single}\ 1\ 1$ fixes $j_0 + q$ and hence `nearCurve j₀`; in particular
every element of the monodromy subgroup of $\mathrm{Aut}_{\bar{\mathbb Q}}(H)$ (the group of twists
$\mathrm{single}\ a\ r \mapsto \mathrm{single}\ a\ (\chi(a)r)$ with $\chi(1) = 1$) does.
`nearTransport j₀ m` is the induced additive automorphism of the points of `nearCurve j₀`, acting
coordinatewise, `b3Act j₀ m` is the induced map on subgroups of the point group, and it carries
$\mathbb Z g$ to $\mathbb Z\,(\text{transport of } g)$.

**Relation to Mathlib.** Mathlib provides `WeierstrassCurve`, its `VariableChange` action and affine
point groups, but not the induced bijection of point groups under a variable change, nor the
reduction of an integral Hahn-series model to its special fibre; both are project notions, as is the
type of cyclic subgroups of a given order used here.

**Where it is used.** These definitions form the specialisation half of the dictionary between roots
of the modular polynomial and cyclic $p$-subgroups: they transfer the subgroup-counting statements
proved for the near model over the Hahn-series field $H$, where the $j$-invariant is transcendental,
to an arbitrary elliptic curve of given $j$-invariant over $\bar{\mathbb Q}$, and record the
monodromy action under which that transfer is equivariant.

<!-- Generated by add_prove2me_provenance.py -->
-/

@[expose] public section publicSection

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.B3

open ModularCurve.TatePoint

theorem map_ofJNe0Or1728 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (j : R) :
    (WeierstrassCurve.ofJNe0Or1728 j).map f = WeierstrassCurve.ofJNe0Or1728 (f j) := by
  simp only [WeierstrassCurve.ofJNe0Or1728, WeierstrassCurve.map, map_sub, map_ofNat, map_zero,
    map_mul, map_neg, map_pow]

theorem equation_specialFibre (W : WeierstrassCurve H) (hW : IntegralCoeffs W) {x y : H}
    (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) (h : W.toAffine.Equation x y) :
    (specialFibre W).toAffine.Equation (x.coeff 0) (y.coeff 0) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  let A₁ : integralO := ⟨W.a₁, h₁⟩
  let A₂ : integralO := ⟨W.a₂, h₂⟩
  let A₃ : integralO := ⟨W.a₃, h₃⟩
  let A₄ : integralO := ⟨W.a₄, h₄⟩
  let A₆ : integralO := ⟨W.a₆, h₆⟩
  let X : integralO := ⟨x, hx⟩
  let Y : integralO := ⟨y, hy⟩
  have h₀ : Y ^ 2 + A₁ * X * Y + A₃ * Y = X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ := by
    apply Subtype.coe_injective
    push_cast
    exact h
  have e := congrArg resO h₀
  simp only [map_add, map_mul, map_pow, resO_apply] at e
  exact e

theorem nonsingular_specialFibre (W : WeierstrassCurve H) (hW : IntegralCoeffs W)
    (hΔ : W.Δ.orderTop = 0) {x y : H} (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop)
    (h : W.toAffine.Nonsingular x y) :
    (specialFibre W).toAffine.Nonsingular (x.coeff 0) (y.coeff 0) := by
  have := isElliptic_specialFibre W hW hΔ
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular]
  exact equation_specialFibre W hW hx hy h.1

def redPoint (W : WeierstrassCurve H) (hW : IntegralCoeffs W) (hΔ : W.Δ.orderTop = 0) :
    W.toAffine.Point → (specialFibre W).toAffine.Point
  | .zero => 0
  | .some x y h =>
    if hxy : 0 ≤ x.orderTop ∧ 0 ≤ y.orderTop then
      WeierstrassCurve.Affine.Point.some (x.coeff 0) (y.coeff 0)
        (nonsingular_specialFibre W hW hΔ hxy.1 hxy.2 h)
    else 0

@[simp] theorem redPoint_zero (W : WeierstrassCurve H) (hW : IntegralCoeffs W)
    (hΔ : W.Δ.orderTop = 0) : redPoint W hW hΔ 0 = 0 := rfl

theorem redPoint_some (W : WeierstrassCurve H) (hW : IntegralCoeffs W)
    (hΔ : W.Δ.orderTop = 0) {x y : H} (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop)
    (h : W.toAffine.Nonsingular x y) :
    redPoint W hW hΔ (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (x.coeff 0) (y.coeff 0)
        (nonsingular_specialFibre W hW hΔ hx hy h) := by
  simp only [redPoint, dite_eq_left (And.intro hx hy)]

universe u

def CycOf (A : Type u) [AddGroup A] (N : ℕ) : Type u :=
  {G : AddSubgroup A // ∃ g : A, addOrderOf g = N ∧ G = AddSubgroup.zmultiples g}

open scoped Classical in
theorem CycSubH_eq_CycOf (E : WeierstrassCurve H) (N : ℕ) :
    CycSubH E N = CycOf E.toAffine.Point N := rfl

theorem CycSub_eq_CycOf (E₀ : WeierstrassCurve Qbar) (N : ℕ) :
    CycSub E₀ N = CycOf E₀.toAffine.Point N := rfl

def cycOfCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (N : ℕ) :
    CycOf A N ≃ CycOf B N where
  toFun G := ⟨G.1.map (e : A →+ B), by
    obtain ⟨g, hg, hG⟩ := G.2
    exact ⟨(e : A →+ B) g, by rw [AddMonoidHom.coe_ofClass, AddEquiv.addOrderOf_eq, hg],
      by rw [hG, AddMonoidHom.map_zmultiples]⟩⟩
  invFun G := ⟨G.1.map (e.symm : B →+ A), by
    obtain ⟨g, hg, hG⟩ := G.2
    exact ⟨(e.symm : B →+ A) g, by rw [AddMonoidHom.coe_ofClass, AddEquiv.addOrderOf_eq, hg],
      by rw [hG, AddMonoidHom.map_zmultiples]⟩⟩
  left_inv G := Subtype.ext ((AddSubgroup.map_symm_eq_iff_map_eq (K := G.1)).mpr rfl)
  right_inv G := Subtype.ext ((AddSubgroup.map_symm_eq_iff_map_eq (K := G.1) (e := e.symm)).mpr rfl)

@[simp] theorem cycOfCongr_apply_coe {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (N : ℕ) (G : CycOf A N) : (cycOfCongr e N G).1 = G.1.map (e : A →+ B) := rfl

theorem mem_torsionBy_of_addOrderOf_eq {A : Type*} [AddCommGroup A] {N : ℕ} {g : A}
    (hg : addOrderOf g = N) : g ∈ Submodule.torsionBy ℤ A N := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← hg, addOrderOf_nsmul_eq_zero]

theorem comap_subtype_zmultiples {A : Type*} [AddCommGroup A] (S : Submodule ℤ A) {x : A}
    (hx : x ∈ S) :
    (AddSubgroup.zmultiples x).comap S.subtype.toAddMonoidHom = AddSubgroup.zmultiples ⟨x, hx⟩ := by
  rw [show AddSubgroup.zmultiples x =
      (AddSubgroup.zmultiples (⟨x, hx⟩ : S)).map S.subtype.toAddMonoidHom from
        (AddMonoidHom.map_zmultiples S.subtype.toAddMonoidHom ⟨x, hx⟩).symm,
    AddSubgroup.comap_map_eq_self_of_injective (Submodule.injective_subtype S)]

def cycOfTorsionBy (A : Type*) [AddCommGroup A] (N : ℕ) :
    CycOf A N ≃ CycOf (Submodule.torsionBy ℤ A N) N where
  toFun G := ⟨G.1.comap (Submodule.torsionBy ℤ A N).subtype.toAddMonoidHom, by
    obtain ⟨g, hg, hG⟩ := G.2
    refine ⟨⟨g, mem_torsionBy_of_addOrderOf_eq hg⟩, ?_, by rw [hG, comap_subtype_zmultiples]⟩
    rw [← addOrderOf_injective (Submodule.torsionBy ℤ A N).subtype.toAddMonoidHom
      (Submodule.injective_subtype _) ⟨g, mem_torsionBy_of_addOrderOf_eq hg⟩]
    exact hg⟩
  invFun G := ⟨G.1.map (Submodule.torsionBy ℤ A N).subtype.toAddMonoidHom, by
    obtain ⟨g, hg, hG⟩ := G.2
    exact ⟨(Submodule.torsionBy ℤ A N).subtype.toAddMonoidHom g,
      by rw [addOrderOf_injective _ (Submodule.injective_subtype _), hg],
      by rw [hG, AddMonoidHom.map_zmultiples]⟩⟩
  left_inv G := by
    apply Subtype.ext
    obtain ⟨g, hg, hG⟩ := G.2
    change (G.1.comap _).map _ = G.1
    apply AddSubgroup.map_comap_eq_self
    rw [hG, AddSubgroup.zmultiples_le]
    exact AddMonoidHom.mem_range.mpr ⟨⟨g, mem_torsionBy_of_addOrderOf_eq hg⟩, rfl⟩
  right_inv G :=
    Subtype.ext (AddSubgroup.comap_map_eq_self_of_injective (Submodule.injective_subtype _) _)

@[simp] theorem cycOfTorsionBy_apply_coe (A : Type*) [AddCommGroup A] (N : ℕ) (G : CycOf A N) :
    (cycOfTorsionBy A N G).1 = G.1.comap (Submodule.torsionBy ℤ A N).subtype.toAddMonoidHom := rfl

@[simp] theorem cycOfTorsionBy_symm_apply_coe (A : Type*) [AddCommGroup A] (N : ℕ)
    (G : CycOf (Submodule.torsionBy ℤ A N) N) :
    ((cycOfTorsionBy A N).symm G).1 = G.1.map (Submodule.torsionBy ℤ A N).subtype.toAddMonoidHom :=
  rfl

def vcAddEquiv {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K)
    (W : WeierstrassCurve K) :
    W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.mk' (WeierstrassCurve.Affine.Point.variableChangeEquiv C W.toAffine).symm
    (WeierstrassCurve.Affine.Point.vcInvFun_add C W.toAffine)

@[simp] theorem vcAddEquiv_apply {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K)
    (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    vcAddEquiv C W P = WeierstrassCurve.Affine.Point.vcInvFun C W.toAffine P := rfl

def pointAddEquivOfEq {K : Type*} [Field K] [DecidableEq K] {W V : WeierstrassCurve K} (h : W = V) :
    W.toAffine.Point ≃+ V.toAffine.Point := by
  subst h; exact AddEquiv.refl _

@[simp] theorem pointAddEquivOfEq_rfl {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ := rfl

instance instIsElliptic_goodModel (j₀ : Qbar) : (goodModel j₀).IsElliptic := by
  unfold goodModel; infer_instance

theorem goodModel_spec (j₀ : Qbar) :
    IntegralCoeffs (goodModel j₀) ∧ (goodModel j₀).Δ.orderTop = 0 := by
  by_cases h0 : j₀ = 0
  · subst h0; exact ⟨goodModel_zero_spec.1, goodModel_zero_spec.2.1⟩
  · by_cases h1728 : j₀ = 1728
    · subst h1728; exact ⟨goodModel_1728_spec.1, goodModel_1728_spec.2.1⟩
    · exact ⟨(goodModel_generic_spec j₀ h0 h1728).1, (goodModel_generic_spec j₀ h0 h1728).2.1⟩

attribute [instance] isElliptic_specialFibre_goodModel

def fibreVC (j₀ : Qbar) : VariableChange Qbar :=
  Classical.choose (exists_variableChange_specialFibre_goodModel j₀)

theorem fibreVC_smul (j₀ : Qbar) :
    fibreVC j₀ • specialFibre (goodModel j₀) = WeierstrassCurve.ofJ j₀ :=
  Classical.choose_spec (exists_variableChange_specialFibre_goodModel j₀)

open scoped Classical in
def scaleAddEquiv (j₀ : Qbar) : (nearCurve j₀).toAffine.Point ≃+ (goodModel j₀).toAffine.Point :=
  vcAddEquiv (scaleVC j₀) (nearCurve j₀)

@[simp] theorem scaleAddEquiv_apply (j₀ : Qbar) (P : (nearCurve j₀).toAffine.Point) :
    scaleAddEquiv j₀ P =
      WeierstrassCurve.Affine.Point.vcInvFun (scaleVC j₀) (nearCurve j₀).toAffine P := rfl

open scoped Classical in
def cycScale (p : ℕ) (j₀ : Qbar) : CycSubH (nearCurve j₀) p ≃ CycSubH (goodModel j₀) p :=
  cycOfCongr (scaleAddEquiv j₀) p

def fibreAddEquiv (j₀ : Qbar) :
    (specialFibre (goodModel j₀)).toAffine.Point ≃+ (WeierstrassCurve.ofJ j₀).toAffine.Point :=
  (vcAddEquiv (fibreVC j₀) (specialFibre (goodModel j₀))).trans (pointAddEquivOfEq (fibreVC_smul
    j₀))

theorem fibreAddEquiv_apply (j₀ : Qbar) (P : (specialFibre (goodModel j₀)).toAffine.Point) :
    fibreAddEquiv j₀ P =
      pointAddEquivOfEq (fibreVC_smul j₀)
        (WeierstrassCurve.Affine.Point.vcInvFun (fibreVC j₀)
          (specialFibre (goodModel j₀)).toAffine P) := rfl

open scoped Classical in
def redTorsionEquiv (W : WeierstrassCurve H) [W.IsElliptic] (hW : IntegralCoeffs W)
    (hΔ : W.Δ.orderTop = 0) [(specialFibre W).IsElliptic] (p : ℕ) [Fact p.Prime] :
    Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ) ≃+
      Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ) :=
  Classical.choose (exists_torsionBy_reduction_addEquiv W hW hΔ p)

open scoped Classical in
theorem redTorsionEquiv_spec (W : WeierstrassCurve H) [W.IsElliptic] (hW : IntegralCoeffs W)
    (hΔ : W.Δ.orderTop = 0) [(specialFibre W).IsElliptic] (p : ℕ) [Fact p.Prime]
    (P : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ)) (x y : H)
    (h : W.toAffine.Nonsingular x y)
    (hP : (P : W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x y h) :
    ∃ h₀ : (specialFibre W).toAffine.Nonsingular (x.coeff 0) (y.coeff 0),
      ((redTorsionEquiv W hW hΔ p P :
            Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ)) :
          (specialFibre W).toAffine.Point) =
        WeierstrassCurve.Affine.Point.some (x.coeff 0) (y.coeff 0) h₀ :=
  Classical.choose_spec (exists_torsionBy_reduction_addEquiv W hW hΔ p) P x y h hP

open scoped Classical in
def cycRed (W : WeierstrassCurve H) [W.IsElliptic] (hW : IntegralCoeffs W) (hΔ : W.Δ.orderTop = 0)
    [(specialFibre W).IsElliptic] (p : ℕ) [Fact p.Prime] :
    CycSubH W p ≃ CycSub (specialFibre W) p :=
  (cycOfTorsionBy W.toAffine.Point p).trans <|
    (cycOfCongr (redTorsionEquiv W hW hΔ p) p).trans
      (cycOfTorsionBy (specialFibre W).toAffine.Point p).symm

def bridge3Specialise (p : ℕ) [Fact p.Prime] [NeZero p] (j₀ : Qbar) :
    CycSubH (nearCurve j₀) p ≃ CycSub (WeierstrassCurve.ofJ j₀) p :=
  (cycScale p j₀).trans <|
    (cycRed (goodModel j₀) (goodModel_spec j₀).1 (goodModel_spec j₀).2 p).trans
      (cycOfCongr (fibreAddEquiv j₀) p)

theorem algebraMap_H_apply (q : Qbar) : (algebraMap Qbar H) q = HahnSeries.C q := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

theorem map_jNear_of_fixes_C_of_fixes_single_one (j₀ : Qbar) (τ : H →+* H)
    (hC : ∀ q : Qbar, τ (HahnSeries.C q) = HahnSeries.C q)
    (h1 : τ (HahnSeries.single (1 : ℚ) (1 : Qbar)) = HahnSeries.single 1 1) :
    τ (jNear j₀) = jNear j₀ := by
  rw [jNear, map_add, hC, h1]

theorem nearCurve_map_of_fixes_jNear (j₀ : Qbar) (τ : H →+* H)
    (hj : τ (jNear j₀) = jNear j₀) :
    (nearCurve j₀).map τ = nearCurve j₀ := by
  rw [nearCurve_eq_ofJNe0Or1728, map_ofJNe0Or1728, hj, ← nearCurve_eq_ofJNe0Or1728]

theorem nearCurve_map_of_fixes_C_of_fixes_single_one (j₀ : Qbar) (τ : H →+* H)
    (hC : ∀ q : Qbar, τ (HahnSeries.C q) = HahnSeries.C q)
    (h1 : τ (HahnSeries.single (1 : ℚ) (1 : Qbar)) = HahnSeries.single 1 1) :
    (nearCurve j₀).map τ = nearCurve j₀ :=
  nearCurve_map_of_fixes_jNear j₀ τ (map_jNear_of_fixes_C_of_fixes_single_one j₀ τ hC h1)

theorem nearCurve_map_of_mem_monodromy (j₀ : Qbar) {m : H ≃ₐ[Qbar] H}
    (hm : m ∈ HahnSeries.monodromy Qbar) :
    (nearCurve j₀).map (m : H →+* H) = nearCurve j₀ :=
  nearCurve_map_of_fixes_C_of_fixes_single_one j₀ (m : H →+* H)
    (fun q => by rw [← algebraMap_H_apply]; exact m.commutes q)
    (HahnSeries.fixes_single_one_of_mem_monodromy hm)

open scoped Classical in
def nearTransport (j₀ : Qbar) (m : HahnSeries.monodromy Qbar) :
    (nearCurve j₀).toAffine.Point ≃+ (nearCurve j₀).toAffine.Point :=
  WeierstrassCurve.Affine.Point.fixedTransport (m : H ≃ₐ[Qbar] H) (nearCurve j₀)
    (nearCurve_map_of_mem_monodromy j₀ m.2)

theorem nearTransport_some (j₀ : Qbar) (m : HahnSeries.monodromy Qbar) (x y : H)
    (h : (nearCurve j₀).toAffine.Nonsingular x y) :
    nearTransport j₀ m (.some x y h) =
      .some ((m : H ≃ₐ[Qbar] H) x) ((m : H ≃ₐ[Qbar] H) y)
        (WeierstrassCurve.Affine.Point.nonsingular_of_fixed _ _
          (nearCurve_map_of_mem_monodromy j₀ m.2) h) := by
  classical
  exact WeierstrassCurve.Affine.Point.fixedTransport_some
    (m : H ≃ₐ[Qbar] H) (nearCurve j₀) (nearCurve_map_of_mem_monodromy j₀ m.2) x y h

open scoped Classical in
def b3Act (j₀ : Qbar) (m : HahnSeries.monodromy Qbar) :
    AddSubgroup (nearCurve j₀).toAffine.Point → AddSubgroup (nearCurve j₀).toAffine.Point :=
  AddSubgroup.map ((nearTransport j₀ m : _ ≃+ _) : _ →+ _)

open scoped Classical in
theorem b3Act_zmultiples (j₀ : Qbar) (m : HahnSeries.monodromy Qbar)
    (g : (nearCurve j₀).toAffine.Point) :
    b3Act j₀ m (AddSubgroup.zmultiples g) = AddSubgroup.zmultiples (nearTransport j₀ m g) :=
  AddMonoidHom.map_zmultiples _ g

end ModularCurve.B3

end

end publicSection
