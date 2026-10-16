/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.HyperbolicPair
public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic

/-!
# Hyperbolic pairs and Siegel–Eichler transvections

The two elementary ingredients of the Witt extension theorem, and hence of Witt cancellation
(`Dias II.6.1–6.4`, `Baeza III.2–III.4`):

* a **hyperbolic pair** in a quadratic module is a pair `u, v` with `q u = q v = 0` and
  `polar q u v = 1`;
* the **Siegel–Eichler transvection** `E(x, y)` attached to `x` isotropic and `y` orthogonal to
  `x` is the isometry `z ↦ z + b(z,x) • y - (b(z,y) + q y * b(z,x)) • x`.

Transvections are the characteristic-2-safe substitute for hyperplane reflections: they are defined
for *every* commutative ring and need no invertible scalar, whereas the reflection `σ_x` requires
`q x` to be a unit. This is why the Dias/Baeza/Knebusch route to cancellation survives
characteristic 2, and it is the reason overview §8 prescribes it over `GN`'s cohomological
proof.

## Main definitions

* `QuadraticForm.plane R` : the hyperbolic plane `(a, b) ↦ a * b` on `R × R`. This is the
  elementary model, defined without dual modules, of `QuadraticForm.dualProd R R`.
* `QuadraticMap.IsHyperbolicPair Q u v` : `Q u = 0`, `Q v = 0`, `polar Q u v = 1`.
* `QuadraticMap.eichler hx hxy` : the transvection, TauCeti's `QuadraticMap.transvection`, as a
  self-isometry of `Q`.
* `QuadraticMap.IsHyperbolicPair.dilation` : the dilation along a hyperbolic pair, TauCeti's
  `TauCeti.QuadraticMap.hyperbolicPairTorus`, as a self-isometry of `Q`.

## Main results

* `QuadraticMap.eichler_apply` : the formula for `E(x, y)`.
* `QuadraticMap.IsHyperbolicPair.decomposition` : any `w` is `b(w,v) • u + b(w,u) • v` plus a
  vector orthogonal to both `u` and `v`. This replaces, in explicit form, the splitting
  `V = ⟨u, v⟩ ⊥ ⟨u, v⟩^⊥` that `Dias II.6.2` uses.
* `QuadraticMap.IsHyperbolicPair.exists_isometryEquiv_of_isUnit` : **the unit case of
  `Dias II.6.2`**. If `i = α • u + β • v + z` with `α` a unit and `z` orthogonal to `u` and `v`,
  then some self-isometry of `Q` carries the hyperbolic pair `(u, v)` to the hyperbolic pair
  `(i, j)`. Reducing the general case to this one is what needs the LG axiom, and is done in
  `QuadraticForm/PlaneTransitivity.lean`.

## References

* I. Dias, *Formas Quadráticas Sobre LG-Anéis*, Ph.D. thesis, Universidade Estadual de Campinas,
  1988, II.6.
* R. Baeza, *Quadratic Forms over Semilocal Rings*, Lecture Notes in Math. **655**, Springer 1978,
  III, (1.5), (1.6), (2.2), (4.2).
-/

@[expose] public section

universe u v w

namespace QuadraticForm

variable (R : Type u) [CommRing R]

/-- The **hyperbolic plane** `(a, b) ↦ a * b` on `R × R`.

This is the elementary model of `QuadraticForm.dualProd R R`, written without dual modules so
that computations with an explicit hyperbolic pair stay computational. -/
def plane : QuadraticForm R (R × R) :=
  QuadraticMap.linMulLin (LinearMap.fst R R R) (LinearMap.snd R R R)

variable {R}

@[simp] theorem plane_apply (x : R × R) : plane R x = x.1 * x.2 := rfl

theorem polar_plane (x y : R × R) :
    QuadraticMap.polar (plane R) x y = x.1 * y.2 + x.2 * y.1 := by
  simp only [QuadraticMap.polar, plane_apply, Prod.fst_add, Prod.snd_add]
  ring

/-- The polar form of the hyperbolic plane at the unit of `R × R` is the sum of the coordinates.
This is the trace of the split quadratic étale algebra. -/
@[simp] theorem polar_plane_one (x : R × R) :
    QuadraticMap.polar (plane R) 1 x = x.1 + x.2 := by
  rw [polar_plane]
  simp [add_comm]

end QuadraticForm

namespace QuadraticMap

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {Q : QuadraticForm R V}

/-! ### Hyperbolic pairs -/

/-- A **hyperbolic pair** of a quadratic module: two isotropic vectors pairing to `1` under the
un-halved polar form. The submodule they span is a hyperbolic plane. -/
structure IsHyperbolicPair (Q : QuadraticForm R V) (u v : V) : Prop where
  /-- The first vector is isotropic. -/
  apply_left : Q u = 0
  /-- The second vector is isotropic. -/
  apply_right : Q v = 0
  /-- The two vectors pair to `1`. -/
  polar_eq_one : polar Q u v = 1

namespace IsHyperbolicPair

variable {u v : V}

theorem symm (h : IsHyperbolicPair Q u v) : IsHyperbolicPair Q v u :=
  ⟨h.apply_right, h.apply_left, by rw [polar_comm]; exact h.polar_eq_one⟩

theorem polar_self_left (h : IsHyperbolicPair Q u v) : polar Q u u = 0 := by
  rw [polar_self, h.apply_left, smul_zero]

theorem polar_self_right (h : IsHyperbolicPair Q u v) : polar Q v v = 0 := by
  rw [polar_self, h.apply_right, smul_zero]

/-- The standard hyperbolic pair of the hyperbolic plane. -/
theorem plane (R : Type u) [CommRing R] :
    IsHyperbolicPair (QuadraticForm.plane R) (1, 0) (0, 1) where
  apply_left := mul_zero 1
  apply_right := zero_mul 1
  polar_eq_one := by rw [QuadraticForm.polar_plane]; ring

/-- **The explicit splitting along a hyperbolic pair.** Every `w` is the sum of its components
along `u` and `v` and a vector orthogonal to both.

This is the computational form of `V = ⟨u, v⟩ ⊥ ⟨u, v⟩^⊥`, and it is all that `Dias II.6.2` uses
of that decomposition. -/
theorem decomposition (h : IsHyperbolicPair Q u v) (w : V) :
    polar Q (w - polar Q w v • u - polar Q w u • v) u = 0 ∧
      polar Q (w - polar Q w v • u - polar Q w u • v) v = 0 := by
  have huv : polar Q u v = 1 := h.polar_eq_one
  have hvu : polar Q v u = 1 := by rw [polar_comm]; exact huv
  constructor
  · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, h.polar_self_left, hvu]
    simp
  · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, h.polar_self_right, huv]
    simp

end IsHyperbolicPair

/-! ### Siegel–Eichler transvections

The transvection, its isometry property and its bijectivity are TauCeti's
`QuadraticMap.transvection`; here it is packaged as a self-isometry of `Q`, with its formula in
the variables used below. -/

/-- The **Siegel–Eichler transvection** `E(x, y)` attached to an isotropic `x` and a vector `y`
orthogonal to it, as a self-isometry of `Q`:
`E(x, y) z = z + b(z, x) • y - (b(z, y) + q y * b(z, x)) • x`. It is TauCeti's
`QuadraticMap.transvection`. Unlike a hyperplane reflection it needs no unit, so it is available
in characteristic 2 and over any commutative ring. -/
noncomputable def eichler {x y : V} (hx : Q x = 0) (hxy : polar Q x y = 0) : Q.IsometryEquiv Q :=
  TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q
    ⟨QuadraticMap.transvection Q hx hxy, QuadraticMap.transvection_mem_orthogonalGroup hx hxy⟩

@[simp] theorem eichler_apply {x y : V} (hx : Q x = 0) (hxy : polar Q x y = 0) (z : V) :
    eichler hx hxy z = z + polar Q x z • y - (polar Q y z + Q y * polar Q x z) • x := by
  simp only [eichler, TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv,
    QuadraticMap.transvection_apply]
  rw [polar_comm Q z x, polar_comm Q z y]
  module

/-- **Building a hyperbolic pair from a dual vector.** If `u` is isotropic and some `w` pairs with
it to `1`, then `(u, -q(w) • u + w)` is a hyperbolic pair. This is the construction in the proof of
`GPR 11.17`, isolated from the hypotheses used to *produce* `w`.

Only additivity is used, so this is valid in characteristic 2: the correction term `-q(w) • u`
replaces the "complete the square" step that would divide by `2`. -/
theorem isHyperbolicPair_neg_smul_add {u w : V} (hu : Q u = 0) (huw : polar Q u w = 1) :
    IsHyperbolicPair Q u (-Q w • u + w) where
  apply_left := hu
  apply_right := by
    have key : ∀ (a : R) (x y : V), Q (a • x + y) = (a * a) * Q x + Q y + a * polar Q x y := by
      intro a x y
      rw [show Q (a • x + y) = Q (a • x) + Q y + polar Q (a • x) y from by rw [polar]; ring,
        Q.map_smul, polar_smul_left, smul_eq_mul, smul_eq_mul]
    rw [key, hu, huw]
    ring
  polar_eq_one := by
    rw [polar_add_right, polar_smul_right, polar_self, hu, huw]
    simp

/-! ### The expansion of `Q` along a hyperbolic pair -/

namespace IsHyperbolicPair

variable {u v : V}

/-- Expanding `Q` on a vector shifted by the two members of a hyperbolic pair. All the identities
below are corollaries of this one computation. -/
theorem apply_add_smul_add_smul (h : IsHyperbolicPair Q u v) (w : V) (s t : R) :
    Q (w + s • u + t • v) = Q w + s * polar Q w u + t * polar Q w v + s * t := by
  have key : ∀ a b : V, Q (a + b) = Q a + Q b + polar Q a b := fun a b ↦ by
    rw [polar]; ring
  rw [key, key, Q.map_smul, Q.map_smul, h.apply_left, h.apply_right]
  simp only [polar_add_left, polar_smul_left, polar_smul_right, h.polar_eq_one, smul_eq_mul,
    mul_zero, add_zero]
  ring

/-- A hyperbolic pair is carried to a hyperbolic pair by an isometry. -/
theorem map {V' : Type w} [AddCommGroup V'] [Module R V'] {Q' : QuadraticForm R V'}
    (h : IsHyperbolicPair Q u v) (f : Q.IsometryEquiv Q') :
    IsHyperbolicPair Q' (f u) (f v) where
  apply_left := by rw [f.map_app]; exact h.apply_left
  apply_right := by rw [f.map_app]; exact h.apply_right
  polar_eq_one := by
    rw [polar, ← map_add, f.map_app, f.map_app, f.map_app, ← polar]
    exact h.polar_eq_one

end IsHyperbolicPair

/-! ### Dilations along a hyperbolic pair -/

namespace IsHyperbolicPair

variable {u v : V}

/-- The **dilation** `φ(l)` attached to a hyperbolic pair `(u, v)` and a unit `l`: it scales `u` by
`l`, scales `v` by `l⁻¹`, and fixes every vector orthogonal to both (`Baeza III §2`'s `P(λ)`,
`Dias II.6`'s `φ(λ)`). It is TauCeti's `TauCeti.QuadraticMap.hyperbolicPairTorus`, packaged as a
self-isometry of `Q`. Unlike a Siegel–Eichler transvection it needs a unit, but only a unit of
`R`, never an invertible value of the form. -/
noncomputable def dilation (h : IsHyperbolicPair Q u v) (l : Rˣ) : Q.IsometryEquiv Q :=
  TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q
    (TauCeti.QuadraticMap.hyperbolicPairTorus Q h.apply_left h.apply_right h.polar_eq_one l)

/-- The dilation `φ(l)` scales `u` by `l`. -/
theorem dilation_left (h : IsHyperbolicPair Q u v) (l : Rˣ) : h.dilation l u = (l : R) • u := by
  simp only [dilation, TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv,
    TauCeti.QuadraticMap.hyperbolicPairTorus_apply_left]

/-! ### Moving one hyperbolic pair to another: the unit case -/

/-- **The unit case of `Dias II.6.2`.** Let `(u, v)` be a hyperbolic pair and let `(i, j)` be
another one whose first vector `i = z + α • u + β • v` has `α` a **unit**, with `z` orthogonal to
`u` and `v`. Then a self-isometry of `Q` carries `(u, v)` to `(i, j)`.

The isometry is an explicit product `E(i, z') ∘ E(v, α⁻¹ • z) ∘ φ(α)` of two Siegel–Eichler
transvections and a dilation, exactly as in `Dias II.6.2` (`Baeza III (4.2)`). Nothing here needs
the base ring to be an LG ring: that hypothesis enters only in reducing the general case to this
one, by producing the unit `α` (`Dias II.6.1`). -/
theorem exists_isometryEquiv_of_isUnit (huv : IsHyperbolicPair Q u v)
    {i j : V} (hij : IsHyperbolicPair Q i j) {a : Rˣ} {b : R} {z : V}
    (hzu : polar Q u z = 0) (hzv : polar Q v z = 0)
    (hi : i = z + (a : R) • u + b • v) :
    ∃ σ : Q.IsometryEquiv Q, σ u = i ∧ σ v = j := by
  set c : R := ((a⁻¹ : Rˣ) : R) with hc
  have hainv : (a : R) * c = 1 := by
    rw [hc, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hvu : polar Q v u = 1 := by rw [polar_comm]; exact huv.polar_eq_one
  -- `Q i = 0` pins down the coefficient `b`.
  have hb : (a : R) * b = -Q z := by
    have hexp := huv.apply_add_smul_add_smul z (a : R) b
    rw [← hi, hij.apply_left, polar_comm Q z u, hzu, polar_comm Q z v, hzv] at hexp
    linear_combination -hexp
  have hb' : b = -(c * Q z) := by linear_combination c * hb - b * hainv
  -- Step 1: `ψ = E(v, α⁻¹ • z) ∘ φ(α)` carries `u` to `i`.
  set y : V := c • z with hy
  have hvy : polar Q v y = 0 := by rw [hy, polar_smul_right, hzv, smul_zero]
  have hyu : polar Q y u = 0 := by
    rw [hy, polar_smul_left, polar_comm Q z u, hzu, smul_zero]
  set ψ : Q.IsometryEquiv Q := (huv.dilation a).trans (eichler huv.apply_right hvy) with hψ
  have hψu : ψ u = i := by
    have hstep : ψ u = eichler huv.apply_right hvy ((a : R) • u) := by
      rw [hψ]
      change eichler huv.apply_right hvy (huv.dilation a u) = _
      rw [huv.dilation_left]
    have hay : (a : R) • y = z := by rw [hy, smul_smul, hainv, one_smul]
    have hQya : Q y * (a : R) = c * Q z := by
      rw [hy, Q.map_smul, smul_eq_mul]
      linear_combination (c * Q z) * hainv
    rw [hstep, eichler_apply, polar_smul_right, hvu, polar_smul_right, hyu, hi, hb']
    simp only [smul_eq_mul, mul_one]
    rw [hQya, hay]
    module
  -- Step 2: `(i, ψ v)` is a hyperbolic pair.
  set w : V := ψ v with hw
  have hiw : IsHyperbolicPair Q i w := by
    have hmap := huv.map ψ
    rwa [hψu] at hmap
  -- Step 3: correct `ψ v` to `j` by one more transvection.
  set z' : V := j - polar Q j w • i - polar Q j i • w with hz'
  obtain ⟨hz'i, hz'w⟩ := hiw.decomposition j
  rw [← hz'] at hz'i hz'w
  have hji : polar Q j i = 1 := by rw [polar_comm]; exact hij.polar_eq_one
  have hjdec : j = z' + polar Q j w • i + (1 : R) • w := by
    rw [hz', hji]; module
  have hlam : polar Q j w = -Q z' := by
    have hexp := hiw.apply_add_smul_add_smul z' (polar Q j w) 1
    rw [← hjdec, hij.apply_right, hz'i, hz'w] at hexp
    linear_combination -hexp
  have hiz' : polar Q i z' = 0 := by rw [polar_comm]; exact hz'i
  refine ⟨ψ.trans (eichler hiw.apply_left hiz'), ?_, ?_⟩
  · change eichler hiw.apply_left hiz' (ψ u) = i
    rw [hψu, eichler_apply, polar_self, hiw.apply_left, polar_comm Q z' i, hiz']
    simp
  · change eichler hiw.apply_left hiz' (ψ v) = j
    rw [← hw, eichler_apply, hiw.polar_eq_one, hz'w, mul_one, zero_add]
    conv_rhs => rw [hjdec, hlam]
    module

end IsHyperbolicPair

end QuadraticMap
