/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.MumfordReduction
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import LeanPool.HyperellipticCurves.ForMathlib.Nakayama
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Cantor composition as a rational map (blueprint `def:cantor-map`, composition stage)

Cantor's composition of Mumford data, in the certificate-passing form dictated by the
genus-2 prototype (`prototype/g2_formal_group.py`): given data `(u₁, v₁)`, `(u₂, v₂)` on
`y² = f(x)` and a **Bézout certificate** `s₁u₁ + s₂u₂ + s₃(v₁+v₂) = 1`, the composed
datum is `(u₁u₂, V)` with `V := ChabautyColeman.cantorV` (all three certificate terms are
genuinely needed: the two-term reductions degenerate at the configurations arising in the
translated formal group law, see the design note in that script).

* Over any commutative ring, `V ≡ vᵢ mod uᵢ` and `u₁u₂ ∣ V² - f` with explicit cofactors
  (`ChabautyColeman.cantorV_sub_left`/`_right`, `ChabautyColeman.cantorV_sq_sub`) — the
  composed datum is again a Mumford datum.
* Over a field, the **ideal-level correctness**
  (`ChabautyColeman.mumfordIdeal_mul_of_bezout`): the product of the two Mumford ideals
  is the Mumford ideal of the composed datum; consequently the composition computes the
  product of the classes in `J(K)` (`ChabautyColeman.mk0_mumfordIdeal_mul_of_bezout`).

* The **reduction step as a rational map on data**: with an inverse certificate
  `c · leadingCoeff w = 1` for the cofactor `w` of `v² - f = u·w`, the normalized reduced
  datum is `(C c · w, (-v) %ₘ (C c · w))` — monic
  (`Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one`), again a Mumford datum
  (`ChabautyColeman.C_mul_cofactor_dvd`), with degree bookkeeping
  (`ChabautyColeman.natDegree_add_natDegree_cofactor`); over a field it represents the
  same class (`ChabautyColeman.mk0_mumfordIdeal_eq_mk0_cofactor_datum`).
* Over a local ring, the **certificate exists** as soon as the reduced data admit one over
  the residue field (`ChabautyColeman.exists_bezout_lift`, by Nakayama via
  `Polynomial.span_eq_top_of_span_image_map_eq_top` — monicity of `u₁` is what makes this
  true).

The file also carries two results the pipelines consume directly: the split-support product
formula `ChabautyColeman.mk0_mumfordIdeal_prod`, and uniqueness of the square root along a
Mumford datum (`ChabautyColeman.eq_of_dvd_sq_sub_of_bezout`, with the residue form
`ChabautyColeman.eq_of_dvd_sq_sub_of_residue_bezout`).

This realizes the content of `def:cantor-map`/`lem:cantor-correct`: every step of the
`Add` algorithm (compose, reduce, normalize) is a polynomial formula in the data and the
certificates, with class-level correctness; the iteration is assembled where it is
consumed (the translated group law `def:Ftau`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Compose

variable {R : Type*} [CommRing R] (f : R[X])

/-- The Cantor composition numerator: given Mumford data `(u₁, v₁)`, `(u₂, v₂)` and a
Bézout certificate `s₁u₁ + s₂u₂ + s₃(v₁+v₂) = 1`, the `v`-part of the composed datum. -/
noncomputable def cantorV (u₁ v₁ u₂ v₂ s₁ s₂ s₃ : R[X]) : R[X] :=
  s₁ * u₁ * v₂ + s₂ * u₂ * v₁ + s₃ * (v₁ * v₂ + f)

variable {u₁ v₁ u₂ v₂ s₁ s₂ s₃ w₁ w₂ : R[X]}

theorem cantorV_sub_left (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₁ : v₁ ^ 2 - f = u₁ * w₁) :
    cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ - v₁ = u₁ * (s₁ * (v₂ - v₁) - s₃ * w₁) := by
  rw [cantorV]
  grobner

theorem cantorV_sub_right (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₂ : v₂ ^ 2 - f = u₂ * w₂) :
    cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ - v₂ = u₂ * (s₂ * (v₁ - v₂) - s₃ * w₂) := by
  rw [cantorV]
  grobner

theorem cantorV_mul_add (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₁ : v₁ ^ 2 - f = u₁ * w₁) (hw₂ : v₂ ^ 2 - f = u₂ * w₂) :
    (v₁ + v₂) * cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ - (v₁ * v₂ + f)
      = u₁ * u₂ * (s₁ * w₂ + s₂ * w₁) := by
  rw [cantorV]
  grobner

/-- **The composed datum lies on the curve**: `u₁u₂` divides `V² - f`, with the explicit
cofactor. -/
theorem cantorV_sq_sub (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₁ : v₁ ^ 2 - f = u₁ * w₁) (hw₂ : v₂ ^ 2 - f = u₂ * w₂) :
    cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ ^ 2 - f
      = u₁ * u₂ * ((s₁ * (v₂ - v₁) - s₃ * w₁) * (s₂ * (v₁ - v₂) - s₃ * w₂)
          + s₁ * w₂ + s₂ * w₁) := by
  have h1 := cantorV_sub_left f hbez hw₁
  have h2 := cantorV_sub_right f hbez hw₂
  have h3 := cantorV_mul_add f hbez hw₁ hw₂
  linear_combination (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ - v₂) * h1
    + u₁ * (s₁ * (v₂ - v₁) - s₃ * w₁) * h2 + h3

end Compose

section Reduce

variable {R : Type*} [CommRing R] (f : R[X]) {u v w : R[X]} {c : R}

theorem C_leadingCoeff_mul_C_mul (hc : c * w.leadingCoeff = 1) :
    C w.leadingCoeff * (C c * w) = w := by
  rw [← mul_assoc, ← C_mul, mul_comm w.leadingCoeff c, hc, C_1, one_mul]

theorem natDegree_C_mul_cofactor (hc : c * w.leadingCoeff = 1) :
    (C c * w).natDegree = w.natDegree := by
  refine le_antisymm (natDegree_C_mul_le c w) ?_
  nth_rw 1 [← C_leadingCoeff_mul_C_mul hc]
  exact natDegree_C_mul_le _ _

/-- **The reduction step preserves the curve relation**: the normalized cofactor datum
`(C c · w, (-v) %ₘ (C c · w))` is again a Mumford datum. -/
theorem C_mul_cofactor_dvd (hw : v ^ 2 - f = u * w) (hc : c * w.leadingCoeff = 1) :
    C c * w ∣ ((-v) %ₘ (C c * w)) ^ 2 - f := by
  have h1 : C c * w ∣ ((-v) %ₘ (C c * w)) ^ 2 - v ^ 2 := by
    rw [← neg_sq v, sq_sub_sq]
    exact (dvd_modByMonic_sub (-v) (C c * w)).mul_left _
  have h2 : C c * w ∣ v ^ 2 - f := by
    rw [hw]
    refine Dvd.dvd.mul_left ?_ u
    exact ⟨C w.leadingCoeff, by rw [mul_comm, C_leadingCoeff_mul_C_mul hc]⟩
  have h := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at h

/-- Degree bookkeeping for the reduction step. -/
theorem natDegree_add_natDegree_cofactor (hu : u.Monic) (hc : c * w.leadingCoeff = 1)
    (hw : v ^ 2 - f = u * w) :
    u.natDegree + w.natDegree = (v ^ 2 - f).natDegree := by
  nontriviality R
  rw [hw, natDegree_mul' (by
    rw [hu.leadingCoeff, one_mul]
    exact right_ne_zero_of_mul_eq_one hc)]

variable {f} in
/-- **Uniqueness of the square root along a Mumford datum**: two polynomials of degree
`< deg U` whose squares agree with `f` modulo `U` are equal, given a Bézout certificate
that `U` is coprime to their sum. -/
theorem eq_of_dvd_sq_sub_of_bezout {U W V a b : R[X]} (hU : U.Monic)
    (hW : U ∣ W ^ 2 - f) (hV : U ∣ V ^ 2 - f) (hdW : W.degree < U.degree)
    (hdV : V.degree < U.degree) (hab : a * U + b * (W + V) = 1) : W = V := by
  have hdvd : U ∣ (W - V) * (W + V) := by
    have h : (W - V) * (W + V) = (W ^ 2 - f) - (V ^ 2 - f) := by ring
    rw [h]
    exact dvd_sub hW hV
  obtain ⟨c, hc⟩ := IsCoprime.dvd_of_dvd_mul_right ⟨a, b, hab⟩ hdvd
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [mul_zero] at hc
    exact sub_eq_zero.mp hc
  · have hlt := (degree_sub_le W V).trans_lt (max_lt hdW hdV)
    rw [hc, degree_mul' (by
      rw [hU.leadingCoeff, one_mul]; exact leadingCoeff_ne_zero.mpr hc0)] at hlt
    exact absurd hlt (not_lt.mpr (le_add_of_nonneg_right (zero_le_degree_iff.mpr hc0)))

end Reduce

section IdealCompose

variable {K : Type*} [Field K] (f : K[X])
variable {u₁ v₁ u₂ v₂ s₁ s₂ s₃ w₁ w₂ : K[X]}

/-- The master identity behind Cantor composition: in the coordinate ring, `y - V` is an
explicit combination of the generators of the product of the two Mumford ideals. -/
theorem y_sub_algebraMap_cantorV (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1) :
    HypRing.y f - algebraMap K[X] (HypRing K f) (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃)
      = algebraMap K[X] (HypRing K f) s₁
          * (algebraMap K[X] _ u₁ * (HypRing.y f - algebraMap K[X] _ v₂))
        + algebraMap K[X] (HypRing K f) s₂
            * (algebraMap K[X] _ u₂ * (HypRing.y f - algebraMap K[X] _ v₁))
        - algebraMap K[X] (HypRing K f) s₃
            * ((HypRing.y f - algebraMap K[X] _ v₁)
              * (HypRing.y f - algebraMap K[X] _ v₂)) := by
  refine QuadraticAlgebra.ext ?_ ?_
  · simp [cantorV, HypRing.y, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
    ring
  · simp [HypRing.y, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
    linear_combination -hbez

-- The three product generators, expressed through the generators `(u₁u₂, y - V)`.
private lemma mul_y_sub_right_eq (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₂ : v₂ ^ 2 - f = u₂ * w₂) :
    algebraMap K[X] (HypRing K f) u₁ * (HypRing.y f - algebraMap K[X] _ v₂)
      = algebraMap K[X] (HypRing K f) u₁
          * (HypRing.y f - algebraMap K[X] _ (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃))
        + algebraMap K[X] (HypRing K f) u₁ * algebraMap K[X] _ u₂
            * (algebraMap K[X] (HypRing K f) s₂
                * (algebraMap K[X] _ v₁ - algebraMap K[X] _ v₂)
              - algebraMap K[X] (HypRing K f) s₃ * algebraMap K[X] _ w₂) := by
  have h2 := congrArg (algebraMap K[X] (HypRing K f)) (cantorV_sub_right f hbez hw₂)
  simp only [map_sub, map_mul] at h2
  linear_combination algebraMap K[X] (HypRing K f) u₁ * h2

private lemma mul_y_sub_left_eq (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₁ : v₁ ^ 2 - f = u₁ * w₁) :
    algebraMap K[X] (HypRing K f) u₂ * (HypRing.y f - algebraMap K[X] _ v₁)
      = algebraMap K[X] (HypRing K f) u₂
          * (HypRing.y f - algebraMap K[X] _ (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃))
        + algebraMap K[X] (HypRing K f) u₁ * algebraMap K[X] _ u₂
            * (algebraMap K[X] (HypRing K f) s₁
                * (algebraMap K[X] _ v₂ - algebraMap K[X] _ v₁)
              - algebraMap K[X] (HypRing K f) s₃ * algebraMap K[X] _ w₁) := by
  have h1 := congrArg (algebraMap K[X] (HypRing K f)) (cantorV_sub_left f hbez hw₁)
  simp only [map_sub, map_mul] at h1
  linear_combination algebraMap K[X] (HypRing K f) u₂ * h1

private lemma y_sub_mul_y_sub_eq (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₁ : v₁ ^ 2 - f = u₁ * w₁) (hw₂ : v₂ ^ 2 - f = u₂ * w₂) :
    (HypRing.y f - algebraMap K[X] (HypRing K f) v₁)
        * (HypRing.y f - algebraMap K[X] _ v₂)
      = -(algebraMap K[X] (HypRing K f) v₁ + algebraMap K[X] _ v₂)
          * (HypRing.y f - algebraMap K[X] _ (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃))
        - algebraMap K[X] (HypRing K f) u₁ * algebraMap K[X] _ u₂
            * (algebraMap K[X] (HypRing K f) s₁ * algebraMap K[X] _ w₂
              + algebraMap K[X] (HypRing K f) s₂ * algebraMap K[X] _ w₁) := by
  have h3 := congrArg (algebraMap K[X] (HypRing K f)) (cantorV_mul_add f hbez hw₁ hw₂)
  simp only [map_sub, map_mul, map_add] at h3
  linear_combination HypRing.y_sq f - h3

open QuadraticAlgebra in
/-- **Cantor composition at the ideal level**: with a Bézout certificate for the data,
the product of two Mumford ideals is the Mumford ideal of the composed datum
(`lem:cantor-correct`, composition stage). -/
theorem mumfordIdeal_mul_of_bezout
    (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f) :
    mumfordIdeal f u₁ v₁ * mumfordIdeal f u₂ v₂
      = mumfordIdeal f (u₁ * u₂) (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃) := by
  obtain ⟨w₁, hw₁⟩ := hd₁
  obtain ⟨w₂, hw₂⟩ := hd₂
  refine le_antisymm ?_ ?_
  · rw [mumfordIdeal_eq_span, mumfordIdeal_eq_span, Ideal.span_mul_span]
    refine Ideal.span_le.mpr ?_
    rintro z ⟨p, hp, q, hq, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    have hu12 : algebraMap K[X] (HypRing K f) (u₁ * u₂)
        ∈ mumfordIdeal f (u₁ * u₂) (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃) :=
      algebraMap_mem_mumfordIdeal f _ _
    have hyVmem : HypRing.y f
          - algebraMap K[X] (HypRing K f) (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃)
        ∈ mumfordIdeal f (u₁ * u₂) (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃) :=
      y_sub_mem_mumfordIdeal f _ _
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · rw [← map_mul]
      exact hu12
    · rw [mul_y_sub_right_eq f hbez hw₂]
      refine add_mem (Ideal.mul_mem_left _ _ hyVmem) ?_
      rw [← map_mul]
      exact Ideal.mul_mem_right _ _ hu12
    · rw [mul_comm (HypRing.y f - algebraMap K[X] (HypRing K f) v₁)
        (algebraMap K[X] (HypRing K f) u₂), mul_y_sub_left_eq f hbez hw₁]
      refine add_mem (Ideal.mul_mem_left _ _ hyVmem) ?_
      rw [← map_mul]
      exact Ideal.mul_mem_right _ _ hu12
    · rw [y_sub_mul_y_sub_eq f hbez hw₁ hw₂]
      refine sub_mem (Ideal.mul_mem_left _ _ hyVmem) ?_
      rw [← map_mul]
      exact Ideal.mul_mem_right _ _ hu12
  · rw [mumfordIdeal_eq_span (v := cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃)]
    refine Ideal.span_le.mpr ?_
    rintro z (rfl | rfl)
    · rw [map_mul]
      exact Ideal.mul_mem_mul (algebraMap_mem_mumfordIdeal f u₁ v₁)
        (algebraMap_mem_mumfordIdeal f u₂ v₂)
    · rw [y_sub_algebraMap_cantorV f hbez]
      refine sub_mem (add_mem ?_ ?_) ?_
      · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul
          (algebraMap_mem_mumfordIdeal f u₁ v₁) (y_sub_mem_mumfordIdeal f u₂ v₂))
      · rw [mul_comm (algebraMap K[X] (HypRing K f) u₂)
          (HypRing.y f - algebraMap K[X] (HypRing K f) v₁)]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul
          (y_sub_mem_mumfordIdeal f u₁ v₁) (algebraMap_mem_mumfordIdeal f u₂ v₂))
      · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul
          (y_sub_mem_mumfordIdeal f u₁ v₁) (y_sub_mem_mumfordIdeal f u₂ v₂))

open nonZeroDivisors in
/-- **Cantor composition computes the product of the classes** (`lem:cantor-correct`,
composition stage, class level). -/
theorem mk0_mumfordIdeal_mul_of_bezout [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)]
    (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    ClassGroup.mk0 ⟨mumfordIdeal f u₁ v₁, mumfordIdeal_mem_nonZeroDivisors f hu₁ v₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f u₂ v₂, mumfordIdeal_mem_nonZeroDivisors f hu₂ v₂⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (u₁ * u₂) (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃),
          mumfordIdeal_mem_nonZeroDivisors f (mul_ne_zero hu₁ hu₂) _⟩ := by
  rw [← MonoidHom.map_mul ClassGroup.mk0]
  exact congrArg ClassGroup.mk0 (Subtype.ext (mumfordIdeal_mul_of_bezout f hbez hd₁ hd₂))

/-- **The class of a split Mumford datum is the product of its point classes**: when the
support splits into distinct linear factors, composing off one point at a time exhibits
the class as the product over the roots. -/
theorem mk0_mumfordIdeal_prod [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)] {ι : Type*} {t : ι → K} {s : Finset ι}
    (hinj : Set.InjOn t s) {V : K[X]}
    (hdvd : (∏ i ∈ s, (X - C (t i))) ∣ V ^ 2 - f) :
    ClassGroup.mk0 ⟨mumfordIdeal f (∏ i ∈ s, (X - C (t i))) V,
        mumfordIdeal_mem_nonZeroDivisors f
          (monic_prod_of_monic s _ fun i _ ↦ monic_X_sub_C (t i)).ne_zero V⟩
      = ∏ i ∈ s, ClassGroup.mk0 ⟨mumfordIdeal f (X - C (t i)) (C (V.eval (t i))),
          mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C (t i)).ne_zero
            (C (V.eval (t i)))⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    conv_rhs => rw [Finset.prod_empty]
    refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
    change (mumfordIdeal f (∏ i ∈ (∅ : Finset ι), (X - C (t i))) V).IsPrincipal
    rw [Finset.prod_empty, mumfordIdeal_one]
    exact ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩
  | insert i s hi ih =>
    -- the sub-datum and the point datum
    have hprod : (X - C (t i)) * ∏ j ∈ s, (X - C (t j)) = ∏ j ∈ insert i s, (X - C (t j))
        := (Finset.prod_insert (f := fun j ↦ X - C (t j)) hi).symm
    have hmul' : ((X - C (t i)) * ∏ j ∈ s, (X - C (t j))) ∣ V ^ 2 - f := by rwa [hprod]
    have hdvds : (∏ j ∈ s, (X - C (t j))) ∣ V ^ 2 - f := (dvd_mul_left _ _).trans hmul'
    have hdvdi : (X - C (t i)) ∣ V ^ 2 - f := (dvd_mul_right _ _).trans hmul'
    have hpt : (V.eval (t i)) ^ 2 = f.eval (t i) := by
      have h := eval_eq_zero_of_dvd_of_eval_eq_zero hdvdi
        (by simp : Polynomial.eval (t i) (X - C (t i)) = 0)
      rw [eval_sub, eval_pow] at h
      exact sub_eq_zero.mp h
    have hdpt : (X - C (t i)) ∣ (C (V.eval (t i)) : K[X]) ^ 2 - f :=
      dvd_iff_isRoot.mpr (by simp [IsRoot, hpt])
    -- coprimality of the point with the rest of the support
    have hcop : IsCoprime ((X : K[X]) - C (t i)) (∏ j ∈ s, (X - C (t j))) := by
      refine IsCoprime.prod_right fun j hj ↦ isCoprime_X_sub_C_of_isUnit_sub ?_
      refine (sub_ne_zero_of_ne fun h ↦ hi ?_).isUnit
      have hij : i = j := hinj (by simp) (by simp [hj]) h
      rwa [hij]
    obtain ⟨s₁, s₂, hbz⟩ := hcop
    have hbez : s₁ * (X - C (t i)) + s₂ * (∏ j ∈ s, (X - C (t j)))
        + 0 * (C (V.eval (t i)) + V) = 1 := by rw [zero_mul, add_zero]; exact hbz
    -- the composition computes the product of the classes
    have hmul := mk0_mumfordIdeal_mul_of_bezout f hbez hdpt hdvds
      (monic_X_sub_C (t i)).ne_zero
      (monic_prod_of_monic s _ fun j _ ↦ monic_X_sub_C (t j)).ne_zero
    -- the composed `v`-part is congruent to `V` modulo the whole support
    have hcongr : mumfordIdeal f ((X - C (t i)) * ∏ j ∈ s, (X - C (t j)))
        (cantorV f (X - C (t i)) (C (V.eval (t i))) (∏ j ∈ s, (X - C (t j))) V s₁ s₂ 0)
        = mumfordIdeal f ((X - C (t i)) * ∏ j ∈ s, (X - C (t j))) V := by
      refine mumfordIdeal_eq_of_dvd_sub f ?_
      obtain ⟨w₁, hw₁⟩ := hdpt
      obtain ⟨w₂, hw₂⟩ := hdvds
      have h1 : (X - C (t i)) ∣ cantorV f (X - C (t i)) (C (V.eval (t i)))
          (∏ j ∈ s, (X - C (t j))) V s₁ s₂ 0 - C (V.eval (t i)) :=
        ⟨_, cantorV_sub_left f hbez hw₁⟩
      have h2 : (∏ j ∈ s, (X - C (t j))) ∣ cantorV f (X - C (t i)) (C (V.eval (t i)))
          (∏ j ∈ s, (X - C (t j))) V s₁ s₂ 0 - V :=
        ⟨_, cantorV_sub_right f hbez hw₂⟩
      have h1' : (X - C (t i)) ∣ cantorV f (X - C (t i)) (C (V.eval (t i)))
          (∏ j ∈ s, (X - C (t j))) V s₁ s₂ 0 - V := by
        have hVpt : (X - C (t i)) ∣ C (V.eval (t i)) - V := by
          rw [← dvd_neg, neg_sub]
          exact X_sub_C_dvd_sub_C_eval
        have h := dvd_add h1 hVpt
        rwa [sub_add_sub_cancel] at h
      exact IsCoprime.mul_dvd ⟨s₁, s₂, hbz⟩ h1' h2
    -- assemble
    have hL : ClassGroup.mk0 ⟨mumfordIdeal f (∏ j ∈ insert i s, (X - C (t j))) V,
        mumfordIdeal_mem_nonZeroDivisors f
          (monic_prod_of_monic (insert i s) _ fun j _ ↦ monic_X_sub_C (t j)).ne_zero V⟩
        = ClassGroup.mk0 ⟨mumfordIdeal f ((X - C (t i)) * ∏ j ∈ s, (X - C (t j)))
            (cantorV f (X - C (t i)) (C (V.eval (t i))) (∏ j ∈ s, (X - C (t j))) V
              s₁ s₂ 0),
            mumfordIdeal_mem_nonZeroDivisors f
              (mul_ne_zero (monic_X_sub_C (t i)).ne_zero
                (monic_prod_of_monic s _ fun j _ ↦ monic_X_sub_C (t j)).ne_zero) _⟩ := by
      refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
      change mumfordIdeal f _ _ = mumfordIdeal f _ _
      rw [hcongr, ← hprod]
    rw [hL, ← hmul, Finset.prod_insert hi,
      ih (hinj.mono (Finset.coe_subset.mpr (Finset.subset_insert i s))) hdvds]

variable {u v w : K[X]} {c : K}

open nonZeroDivisors in
/-- **Class-level correctness of the full reduction step** (`lem:cantor-correct`,
reduction stage): over a field, the normalized reduced cofactor datum represents the same
ideal class. -/
theorem mk0_mumfordIdeal_eq_mk0_cofactor_datum [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)] (hu : u ≠ 0) (hw0 : w ≠ 0) (hc : c * w.leadingCoeff = 1)
    (hvw : v ^ 2 - f = u * w) :
    ClassGroup.mk0 ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hu v⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (C c * w) ((-v) %ₘ (C c * w)),
          mumfordIdeal_mem_nonZeroDivisors f
            (mul_ne_zero (C_ne_zero.mpr (left_ne_zero_of_mul_eq_one hc)) hw0) _⟩ := by
  have hCc : c ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hid : mumfordIdeal f (C c * w) ((-v) %ₘ (C c * w)) = mumfordIdeal f w (-v) := by
    rw [mumfordIdeal_modByMonic f (C c * w) (-v), mumfordIdeal_C_mul f hCc]
  rw [mk0_mumfordIdeal_eq_mk0_cofactor_neg f hu hw0 hvw]
  exact congrArg ClassGroup.mk0 (Subtype.ext hid.symm)

end IdealCompose

section CertificateExists

open IsLocalRing

/-- **Prescribed-residue certificate lifting**: a Bézout certificate over the image ring
lifts to one over `R` mapping onto it, provided the first polynomial is monic and the
kernel of `φ` is contained in the Jacobson radical (Nakayama; monicity of `u` is
essential — `u = 1 - πX` over a DVR has unit reduction but generates a proper ideal).
Prescribing the residues is what makes residue-level pipeline computations transportable
along the lifted certificates. -/
theorem exists_bezout_lift_map {R A : Type*} [CommRing R] [CommRing A] {φ : R →+* A}
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ ≤ Ideal.jacobson ⊥)
    {u g h : R[X]} (hu : u.Monic)
    {a b c : A[X]} (habc : a * u.map φ + b * g.map φ + c * h.map φ = 1) :
    ∃ s₁ s₂ s₃ : R[X], s₁ * u + s₂ * g + s₃ * h = 1
      ∧ s₁.map φ = a ∧ s₂.map φ = b ∧ s₃.map φ = c := by
  -- the images generate the unit ideal, hence so do the polynomials themselves (Nakayama)
  have hbar : Ideal.span {u.map φ, g.map φ, h.map φ} = ⊤ := by
    refine (Ideal.eq_top_iff_one _).mpr ?_
    rw [← habc]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have htop : Ideal.span {u, g, h} = ⊤ :=
    span_eq_top_of_span_image_map_eq_top hsurj hker ⟨u, Set.mem_insert u _, hu⟩
      (by rwa [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton])
  have h1 : (1 : R[X]) ∈ Ideal.span {u, g, h} := htop ▸ trivial
  rw [Ideal.mem_span_insert] at h1
  obtain ⟨t₁, z, hz, hz1⟩ := h1
  obtain ⟨t₂, t₃, rfl⟩ := Ideal.mem_span_pair.mp hz
  have hs : t₁ * u + t₂ * g + t₃ * h = 1 := by linear_combination -hz1
  -- lift the prescribed certificate arbitrarily and correct the error inside the span
  obtain ⟨a₀, rfl⟩ := Polynomial.map_surjective φ hsurj a
  obtain ⟨b₀, rfl⟩ := Polynomial.map_surjective φ hsurj b
  obtain ⟨c₀, rfl⟩ := Polynomial.map_surjective φ hsurj c
  have he : (a₀ * u + b₀ * g + c₀ * h - 1).map φ = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_one, habc, sub_self]
  refine ⟨a₀ - (a₀ * u + b₀ * g + c₀ * h - 1) * t₁, b₀ - (a₀ * u + b₀ * g + c₀ * h - 1) * t₂,
    c₀ - (a₀ * u + b₀ * g + c₀ * h - 1) * t₃,
    by linear_combination (1 - (a₀ * u + b₀ * g + c₀ * h)) * hs, ?_, ?_, ?_⟩ <;>
    rw [Polynomial.map_sub, Polynomial.map_mul, he, zero_mul, sub_zero]

/-- **Coprimality with a monic polynomial is detected by the residue**: the Bézout
certificate for the images lifts by `ChabautyColeman.exists_bezout_lift_map`. -/
theorem isCoprime_of_map {R A : Type*} [CommRing R] [CommRing A] {φ : R →+* A}
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ ≤ Ideal.jacobson ⊥) {u g : R[X]}
    (hu : u.Monic) (hco : IsCoprime (u.map φ) (g.map φ)) : IsCoprime u g := by
  obtain ⟨a, b, hab⟩ := hco
  have habc : a * u.map φ + b * g.map φ + (0 : A[X]) * (0 : R[X]).map φ = 1 := by
    rwa [Polynomial.map_zero, mul_zero, add_zero]
  obtain ⟨s₁, s₂, s₃, hs, -, -, -⟩ := exists_bezout_lift_map hsurj hker hu habc
  rw [mul_zero, add_zero] at hs
  exact ⟨s₁, s₂, hs⟩

variable {O : Type*} [CommRing O] [IsLocalRing O] {u g h : O[X]}

/-- **Certificate existence over a local ring**: if `u` is monic and the reductions of
`(u, g, h)` admit a Bézout certificate over the residue field, then `(u, g, h)` admit one
over `O` itself. This produces the certificate hypothesis `hbez` of the composition
lemmas above from a residue-field computation. -/
theorem exists_bezout_lift (hu : u.Monic)
    (hbez : ∃ a b c : (ResidueField O)[X],
      a * u.map (residue O) + b * g.map (residue O) + c * h.map (residue O) = 1) :
    ∃ s₁ s₂ s₃ : O[X], s₁ * u + s₂ * g + s₃ * h = 1 := by
  obtain ⟨a, b, c, habc⟩ := hbez
  obtain ⟨s₁, s₂, s₃, hs, -, -, -⟩ := exists_bezout_lift_map residue_surjective
    (ker_residue.trans_le (maximalIdeal_le_jacobson ⊥)) hu habc
  exact ⟨s₁, s₂, s₃, hs⟩

/-- **Separability is detected by the residue**: the Bézout certificate for `(ū, ū')` lifts
by `ChabautyColeman.exists_bezout_lift`. -/
theorem separable_of_map_residue (hu : u.Monic) (hsep : (u.map (residue O)).Separable) :
    u.Separable := by
  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨s₁, s₂, s₃, hs⟩ := exists_bezout_lift (g := derivative u) (h := 0) hu
    ⟨a, b, 0, by
      rw [Polynomial.map_zero, mul_zero, add_zero, ← derivative_map]
      exact hab⟩
  rw [mul_zero, add_zero] at hs
  exact ⟨s₁, s₂, by rw [Polynomial.derivative] at hs ⊢; exact hs⟩

open IsLocalRing in
/-- **Square-root uniqueness from residue data**: two square roots of `f` modulo a monic
`U` of bounded degree whose residues agree are equal, provided a Bézout certificate for
`(ū, 2v_bar)` exists at the common residue datum — the certificate for the sum `W + V`
lifts by `ChabautyColeman.exists_bezout_lift`. -/
theorem eq_of_dvd_sq_sub_of_residue_bezout {f v U W V : O[X]}
    {c₁ c₂ : (ResidueField O)[X]} (hU : U.Monic)
    (hW : U ∣ W ^ 2 - f) (hV : U ∣ V ^ 2 - f) (hdW : W.degree < U.degree)
    (hdV : V.degree < U.degree)
    (hbez : c₁ * U.map (residue O) + c₂ * (2 * v.map (residue O)) = 1)
    (hWres : W.map (residue O) = v.map (residue O))
    (hVres : V.map (residue O) = v.map (residue O)) : W = V := by
  obtain ⟨a, b, c, habc⟩ := exists_bezout_lift (g := W + V) (h := 0) hU
    ⟨c₁, c₂, 0, by
      rw [Polynomial.map_zero, mul_zero, add_zero, Polynomial.map_add, hWres, hVres,
        ← two_mul]
      exact hbez⟩
  rw [mul_zero, add_zero] at habc
  exact eq_of_dvd_sq_sub_of_bezout hU hW hV hdW hdV habc

end CertificateExists

end ChabautyColeman

end
