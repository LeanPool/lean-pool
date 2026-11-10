/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.Jacobian

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# Cantor reduction: existence of reduced Mumford representatives

Every class in `J(K)` is the class of a *reduced* Mumford ideal `(u, y - v)`:
`u` monic, `deg v < deg u` and `deg u ≤ g` (where `deg f = 2g + 1`); this is
`ChabautyColeman.exists_mk0_mumfordIdeal_reduced`, the existence half of the Mumford
representation.

The proof is Cantor's reduction: normalization lemmas show that the Mumford ideal is
unchanged by unit rescaling of `u` and by reducing `v` mod `u`; the descent step
replaces `(u, v)` by `(w, -v)` with `v² - f = u·w` — a class-preserving move by the
divisor identity for `y - v` and the conjugation identity — and strictly decreases
`deg u` while `deg u > g`.

We then prove that the reduced representative is *unique*
(`ChabautyColeman.mumfordIdeal_reduced_unique`): the connecting ideal
`(u₁, y - v₁)·ι(u₂, y - v₂)` of two equivalent reduced Mumford ideals is an integral
principal ideal `(h)`, whose norm generates `(u₁u₂)` of degree `≤ 2g`; since elements
with `im ≠ 0` have norm of degree `≥ 2g + 1`, `h` lies in `K[x]`, and comparing traces
on `K[x]` forces `u₁ = u₂`, then equality of the ideals, then `v₁ = v₂`.

Blueprint nodes: `lem:mumford-reduce`, `lem:mumford-exists`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

open QuadraticAlgebra Ideal nonZeroDivisors

variable {K : Type*} [Field K] (f : K[X]) {u v w : K[X]}

-- unit rescaling of the first generator
private lemma span_pair_unit_mul {R : Type*} [CommRing R] {w : R} (hw : IsUnit w) (a b : R) :
    Ideal.span {w * a, b} = Ideal.span {a, b} := by
  rw [Ideal.span_insert, Ideal.span_singleton_mul_left_unit hw, ← Ideal.span_insert]

theorem mumfordIdeal_C_mul {c : K} (hc : c ≠ 0) (u v : K[X]) :
    mumfordIdeal f (C c * u) v = mumfordIdeal f u v := by
  rw [mumfordIdeal_eq_span, mumfordIdeal_eq_span, map_mul]
  exact span_pair_unit_mul ((Polynomial.isUnit_C.mpr hc.isUnit).map _) _ _

theorem mumfordIdeal_mul_leadingCoeff_inv (hu : u ≠ 0) :
    mumfordIdeal f (u * C u.leadingCoeff⁻¹) v = mumfordIdeal f u v := by
  rw [mul_comm]
  exact mumfordIdeal_C_mul f (inv_ne_zero (leadingCoeff_ne_zero.mpr hu)) u v

theorem mumfordIdeal_add_mul (u v q : K[X]) :
    mumfordIdeal f u (v + u * q) = mumfordIdeal f u v := by
  have hgen : HypRing.y f - algebraMap K[X] (HypRing K f) (v + u * q)
      = (HypRing.y f - algebraMap K[X] (HypRing K f) v)
        + (-(algebraMap K[X] (HypRing K f) q)) * algebraMap K[X] (HypRing K f) u := by
    rw [map_add, map_mul]
    ring
  rw [mumfordIdeal_eq_span, mumfordIdeal_eq_span, hgen]
  exact Ideal.span_pair_add_mul_left (algebraMap K[X] (HypRing K f) u)
    (HypRing.y f - algebraMap K[X] (HypRing K f) v) (-(algebraMap K[X] (HypRing K f) q))

theorem mumfordIdeal_modByMonic (u v : K[X]) :
    mumfordIdeal f u (v %ₘ u) = mumfordIdeal f u v := by
  conv_rhs => rw [← modByMonic_add_div v u]
  exact (mumfordIdeal_add_mul f u (v %ₘ u) (v /ₘ u)).symm

lemma dvd_modByMonic_sq_sub (h : u ∣ v ^ 2 - f) : u ∣ (v %ₘ u) ^ 2 - f := by
  have hmod : v %ₘ u = v - u * (v /ₘ u) := eq_sub_iff_add_eq.mpr (modByMonic_add_div v u)
  have h1 : u ∣ (v %ₘ u) ^ 2 - v ^ 2 := ⟨(v /ₘ u) * ((v %ₘ u) + v) * (-1), by
    rw [hmod]; ring⟩
  have := dvd_add h1 h
  rwa [sub_add_sub_cancel] at this

/-! ### Traces of Mumford ideals on `K[x]` -/

/-- Membership in a Mumford ideal, componentwise: `z ∈ (u, y - v)` iff `u ∣ re z + im z · v`. -/
theorem mem_mumfordIdeal_iff (h : u ∣ v ^ 2 - f) {z : HypRing K f} :
    z ∈ mumfordIdeal f u v ↔ u ∣ z.re + z.im * v := by
  rw [← ker_mumfordHom f h, RingHom.mem_ker, mumfordHom_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_span_singleton]

/-- The trace of a Mumford ideal on `K[x]` is `(u)`. -/
theorem comap_mumfordIdeal (h : u ∣ v ^ 2 - f) :
    (mumfordIdeal f u v).comap (algebraMap K[X] (HypRing K f)) = Ideal.span {u} := by
  ext p
  rw [Ideal.mem_comap, mem_mumfordIdeal_iff f h, mem_span_singleton]
  simp

/-- The trace on `K[x]` of a `K[x]`-rescaled ideal. -/
theorem comap_span_singleton_mul (x : K[X]) (hx : x ≠ 0) (I : Ideal (HypRing K f)) :
    (Ideal.span {algebraMap K[X] (HypRing K f) x} * I).comap (algebraMap K[X] (HypRing K f))
      = Ideal.span {x} * I.comap (algebraMap K[X] (HypRing K f)) := by
  ext p
  rw [Ideal.mem_comap, Ideal.mem_span_singleton_mul, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨z, hz, hzp⟩
    have hre := congrArg QuadraticAlgebra.re hzp
    have him := congrArg QuadraticAlgebra.im hzp
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_algebraMap,
      QuadraticAlgebra.im_algebraMap, mul_zero, zero_mul, add_zero] at hre him
    have hzim : z.im = 0 := (mul_eq_zero.mp him).resolve_left hx
    have hzre := (QuadraticAlgebra.eq_algebraMap_re hzim).symm
    refine ⟨z.re, ?_, hre⟩
    rwa [Ideal.mem_comap, hzre]
  · rintro ⟨q, hq, rfl⟩
    exact ⟨algebraMap K[X] _ q, Ideal.mem_comap.mp hq, by rw [← map_mul]⟩

theorem map_star_map_star (I : Ideal (HypRing K f)) :
    (I.map (starRingEnd (HypRing K f))).map (starRingEnd (HypRing K f)) = I := by
  rw [Ideal.map_map, RingHomInvPair.comp_eq, Ideal.map_id]

theorem map_star_span_singleton (h : HypRing K f) :
    (Ideal.span {h}).map (starRingEnd (HypRing K f)) = Ideal.span {star h} := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

lemma comap_span_singleton_algebraMap {x : K[X]} (hx : x ≠ 0) :
    (Ideal.span {algebraMap K[X] (HypRing K f) x}).comap (algebraMap K[X] (HypRing K f))
      = Ideal.span {x} := by
  have h := comap_span_singleton_mul f x hx ⊤
  rwa [mul_top, Ideal.comap_top, mul_top] at h

-- The trace on `K[x]` of a rescaling identity between Mumford ideals.
private lemma comap_span_mul_mumfordIdeal {a b p₁ q₁ p₂ q₂ : K[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hd₁ : p₁ ∣ q₁ ^ 2 - f) (hd₂ : p₂ ∣ q₂ ^ 2 - f)
    (heq : Ideal.span {algebraMap K[X] (HypRing K f) a} * mumfordIdeal f p₁ q₁
      = Ideal.span {algebraMap K[X] (HypRing K f) b} * mumfordIdeal f p₂ q₂) :
    Ideal.span ({a * p₁} : Set K[X]) = Ideal.span {b * p₂} := by
  have hcm := congrArg (Ideal.comap (algebraMap K[X] (HypRing K f))) heq
  rwa [comap_span_singleton_mul f a ha, comap_span_singleton_mul f b hb,
    comap_mumfordIdeal f hd₁, comap_mumfordIdeal f hd₂,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton] at hcm

variable [Fact (Odd f.natDegree)]

instance instFaithfulSMulPoly : FaithfulSMul K[X] (HypRing K f) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr QuadraticAlgebra.algebraMap_injective

lemma map_star_mem_nonZeroDivisors {I : Ideal (HypRing K f)}
    (hI : I ∈ (Ideal (HypRing K f))⁰) :
    I.map (starRingEnd (HypRing K f)) ∈ (Ideal (HypRing K f))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero] at hI ⊢
  rwa [ne_eq, Submodule.zero_eq_bot,
    Ideal.map_eq_bot_iff_of_injective star_injective, ← Submodule.zero_eq_bot]

private lemma natDegree_norm_ge {z : HypRing K f} (him : z.im ≠ 0) :
    f.natDegree ≤ (Algebra.norm K[X] z).natDegree := by
  have hf : Odd f.natDegree := Fact.out
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf.pos
  have h1 : (f * z.im ^ 2).natDegree = f.natDegree + 2 * z.im.natDegree := by
    rw [natDegree_mul hf0 (pow_ne_zero 2 him), natDegree_pow]
  have hne : (z.re ^ 2).natDegree ≠ (f * z.im ^ 2).natDegree := by
    rw [natDegree_pow, h1]
    obtain ⟨k, hk⟩ := hf
    lia
  rw [HypRing.norm_eq]
  rcases Nat.lt_or_ge (z.re ^ 2).natDegree (f * z.im ^ 2).natDegree with hlt | hge
  · rw [natDegree_sub_eq_right_of_natDegree_lt hlt, h1]
    lia
  · have hlt : (f * z.im ^ 2).natDegree < (z.re ^ 2).natDegree := lt_of_le_of_ne hge (Ne.symm hne)
    rw [natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_pow]
    rw [natDegree_pow, h1] at hlt
    lia

-- v² - f never vanishes (f is not a square, having odd degree)
lemma sq_sub_ne_zero (v : K[X]) : v ^ 2 - f ≠ 0 := by
  intro h
  have hf : Odd f.natDegree := Fact.out
  rw [show f = v ^ 2 by linear_combination -h, natDegree_pow] at hf
  obtain ⟨k, hk⟩ := hf
  lia

theorem mumfordIdeal_mem_nonZeroDivisors {u : K[X]} (hu : u ≠ 0) (v : K[X]) :
    mumfordIdeal f u v ∈ (Ideal (HypRing K f))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (mumfordIdeal_ne_zero f hu v)

/-- **A generator of the connecting ideal is a polynomial**: if the norm of `h` generates
`(u₁·u₂)` and both `u`-degrees are below half the degree of `f`, then `h` has no `y`-part,
so it is fixed by the conjugation. -/
private theorem eq_algebraMap_re_of_span_norm {u₁ u₂ : K[X]} {h : HypRing K f}
    (hu₁0 : u₁ ≠ 0) (hu₂0 : u₂ ≠ 0) (hg₁ : 2 * u₁.natDegree < f.natDegree)
    (hg₂ : 2 * u₂.natDegree < f.natDegree)
    (hnorm : Ideal.span {Algebra.norm K[X] h} = Ideal.span {u₁ * u₂}) :
    h = algebraMap K[X] (HypRing K f) h.re ∧ star h = h := by
  have him0 : h.im = 0 := by
    by_contra him
    obtain ⟨c, hc⟩ := Ideal.span_singleton_eq_span_singleton.mp hnorm
    have hN0 : Algebra.norm K[X] h ≠ 0 := fun h0 ↦ by
      rw [h0, zero_mul] at hc
      exact mul_ne_zero hu₁0 hu₂0 hc.symm
    have h2 : (Algebra.norm K[X] h).natDegree = u₁.natDegree + u₂.natDegree := by
      have := congrArg natDegree hc
      rwa [natDegree_mul hN0 (Units.ne_zero c), natDegree_eq_zero_of_isUnit c.isUnit, add_zero,
        natDegree_mul hu₁0 hu₂0] at this
    lia [natDegree_norm_ge f him]
  have hha := QuadraticAlgebra.eq_algebraMap_re him0
  exact ⟨hha, by rw [hha, QuadraticAlgebra.star_algebraMap]⟩

variable [NeZero (2 : K)] [Fact (Squarefree f)]

open nonZeroDivisors in
/-- The involution inverts the class of a Mumford ideal: `[ι(𝔞_{u,v})] = [𝔞_{u,v}]⁻¹` in `J(K)` —
the Mumford-level instance of the general norm identity `lem:iota-norm` (formalized in
`upstream HyperellipticCurves.Archive.ConjugateIdealNorm`), directly from the Mumford norm identity.
-/
theorem classGroup_mk0_mumfordIdeal_map_star {u v : K[X]} (h : u ∣ v ^ 2 - f) (hu : u ≠ 0)
    (hmem : mumfordIdeal f u v ∈ (Ideal (HypRing K f))⁰) :
    ClassGroup.mk0 ⟨(mumfordIdeal f u v).map (starRingEnd (HypRing K f)),
        map_star_mem_nonZeroDivisors f hmem⟩
      = (ClassGroup.mk0 ⟨mumfordIdeal f u v, hmem⟩)⁻¹ := by
  refine ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨algebraMap K[X] _ u,
    (map_ne_zero_iff _ QuadraticAlgebra.algebraMap_injective).mpr hu, ?_⟩
  change (mumfordIdeal f u v).map (starRingEnd (HypRing K f)) * mumfordIdeal f u v = _
  rw [mul_comm, mumfordIdeal_mul_map_star f Fact.out (NeZero.ne 2) h]

private lemma mk0_congr {I J : Ideal (HypRing K f)} (hI : I ∈ (Ideal (HypRing K f))⁰)
    (hJ : J ∈ (Ideal (HypRing K f))⁰) (h : I = J) :
    ClassGroup.mk0 ⟨I, hI⟩ = ClassGroup.mk0 ⟨J, hJ⟩ :=
  congrArg _ (Subtype.ext h)

/-- The Cantor reduction step at class level: for `v² - f = u·w`,
`[(u, y - v)] = [(w, y + v)]` in `J(K)`. -/
theorem mk0_mumfordIdeal_eq_mk0_cofactor_neg (hu : u ≠ 0) (hw0 : w ≠ 0)
    (hvw : v ^ 2 - f = u * w) :
    ClassGroup.mk0 ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hu v⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f w (-v),
        mumfordIdeal_mem_nonZeroDivisors f hw0 (-v)⟩ := by
  rw [classGroup_mk0_mumfordIdeal_cofactor f hvw hu hw0,
    ← classGroup_mk0_mumfordIdeal_map_star f ⟨u, by rw [hvw]; ring⟩ hw0
      (mumfordIdeal_mem_nonZeroDivisors f hw0 v)]
  exact congrArg _ (Subtype.ext (map_star_mumfordIdeal f w v))

private lemma descend (n : ℕ) : ∀ u v : K[X], ∀ (hm : u.Monic), u.natDegree ≤ n →
    u ∣ v ^ 2 - f →
    ∃ (u' v' : K[X]) (hm' : u'.Monic), v'.degree < u'.degree ∧
      2 * u'.natDegree < f.natDegree ∧ u' ∣ v' ^ 2 - f ∧
      ClassGroup.mk0 ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hm.ne_zero v⟩
        = ClassGroup.mk0 ⟨mumfordIdeal f u' v',
            mumfordIdeal_mem_nonZeroDivisors f hm'.ne_zero v'⟩ := by
  induction n with
  | zero =>
    intro u v hm hn hdvd
    have hu1 : u = 1 := eq_one_of_monic_natDegree_zero hm (Nat.le_zero.mp hn)
    subst hu1
    refine ⟨1, 0, monic_one, ?_, ?_, one_dvd _, ?_⟩
    · simp [degree_one]
    · have hf : Odd f.natDegree := Fact.out
      simpa using hf.pos
    · refine mk0_congr f _ _ ?_
      have htop (v' : K[X]) : mumfordIdeal f 1 v' = ⊤ := by
        rw [Ideal.eq_top_iff_one]
        simpa using algebraMap_mem_mumfordIdeal f 1 v'
      rw [htop v, htop 0]
  | succ n ih =>
    intro u v hm hn hdvd
    by_cases hred : 2 * u.natDegree < f.natDegree
    · exact ⟨u, v %ₘ u, hm, degree_modByMonic_lt v hm, hred, dvd_modByMonic_sq_sub f hdvd,
        mk0_congr f _ _ (mumfordIdeal_modByMonic f u v).symm⟩
    · have hu0 : u ≠ 0 := hm.ne_zero
      have hfpos : 1 ≤ u.natDegree := by lia [(Fact.out : Odd f.natDegree).pos]
      have hdvd₁ : u ∣ (v %ₘ u) ^ 2 - f := dvd_modByMonic_sq_sub f hdvd
      obtain ⟨w, hw⟩ := hdvd₁
      have hne : (v %ₘ u) ^ 2 - f ≠ 0 := sq_sub_ne_zero f (v %ₘ u)
      have hw0 : w ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hw
        exact hne hw
      have hvdeg : (v %ₘ u).natDegree < u.natDegree := by
        rcases eq_or_ne (v %ₘ u) 0 with h0 | h0
        · rw [h0, natDegree_zero]
          lia
        · exact natDegree_lt_natDegree h0 (degree_modByMonic_lt v hm)
      have hdeg : w.natDegree < u.natDegree := by
        have h1 : u.natDegree + w.natDegree = ((v %ₘ u) ^ 2 - f).natDegree := by
          rw [hw, natDegree_mul hu0 hw0]
        have h2 : ((v %ₘ u) ^ 2 - f).natDegree ≤ max (2 * (v %ₘ u).natDegree) f.natDegree := by
          refine (natDegree_sub_le _ _).trans ?_
          rw [natDegree_pow]
        have hf : Odd f.natDegree := Fact.out
        obtain ⟨k, hk⟩ := hf
        rcases max_cases (2 * (v %ₘ u).natDegree) f.natDegree with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
          rw [hmax] at h2 <;> lia
      -- monicize w
      have hcm : (w * C w.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hw0
      have hdvdw : w * C w.leadingCoeff⁻¹ ∣ (-(v %ₘ u)) ^ 2 - f :=
        (mul_leadingCoeff_inv_dvd_iff hw0).mpr ⟨u, by rw [neg_sq, hw, mul_comm]⟩
      have hndw : (w * C w.leadingCoeff⁻¹).natDegree ≤ n := by
        rw [natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_inv w hw0)]
        lia
      obtain ⟨u', v', hm', hlt', hred', hdvd', heq'⟩ :=
        ih (w * C w.leadingCoeff⁻¹) (-(v %ₘ u)) hcm hndw hdvdw
      refine ⟨u', v', hm', hlt', hred', hdvd', ?_⟩
      calc ClassGroup.mk0 ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hu0 v⟩
          = ClassGroup.mk0 ⟨mumfordIdeal f u (v %ₘ u), mumfordIdeal_mem_nonZeroDivisors f hu0 _⟩ :=
            mk0_congr f _ _ (mumfordIdeal_modByMonic f u v).symm
        _ = ClassGroup.mk0 ⟨mumfordIdeal f w (-(v %ₘ u)),
              mumfordIdeal_mem_nonZeroDivisors f hw0 _⟩ :=
            mk0_mumfordIdeal_eq_mk0_cofactor_neg f hu0 hw0 hw
        _ = ClassGroup.mk0 ⟨mumfordIdeal f (w * C w.leadingCoeff⁻¹) (-(v %ₘ u)),
              mumfordIdeal_mem_nonZeroDivisors f hcm.ne_zero _⟩ :=
            mk0_congr f _ _ (mumfordIdeal_mul_leadingCoeff_inv f hw0).symm
        _ = ClassGroup.mk0 ⟨mumfordIdeal f u' v',
              mumfordIdeal_mem_nonZeroDivisors f hm'.ne_zero v'⟩ := heq'

/-- Existence of reduced Mumford representatives: every class in `J(K)` is the class of
a Mumford ideal `(u, y - v)` with `u` monic, `deg v < deg u` and `deg u ≤ g`
(where `deg f = 2g + 1`). -/
theorem exists_mk0_mumfordIdeal_reduced (x : ClassGroup (HypRing K f)) :
    ∃ (u v : K[X]) (hm : u.Monic), v.degree < u.degree ∧ 2 * u.natDegree < f.natDegree ∧
      u ∣ v ^ 2 - f ∧
      x = ClassGroup.mk0 ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hm.ne_zero v⟩ := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  obtain ⟨u₀, v₀, hu₀, hdvd₀, heq₀⟩ := exists_mk0_eq_mk0_mumfordIdeal f I.1 I.2
  have hm₀ : (u₀ * C u₀.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hu₀
  have hdvdm : u₀ * C u₀.leadingCoeff⁻¹ ∣ v₀ ^ 2 - f :=
    (mul_leadingCoeff_inv_dvd_iff hu₀).mpr hdvd₀
  obtain ⟨u, v, hm, hlt, hred, hdvd, heq⟩ := descend f (u₀ * C u₀.leadingCoeff⁻¹).natDegree
    (u₀ * C u₀.leadingCoeff⁻¹) v₀ hm₀ le_rfl hdvdm
  refine ⟨u, v, hm, hlt, hred, hdvd, ?_⟩
  calc ClassGroup.mk0 I = ClassGroup.mk0 ⟨mumfordIdeal f u₀ v₀, _⟩ := heq₀
    _ = ClassGroup.mk0 ⟨mumfordIdeal f (u₀ * C u₀.leadingCoeff⁻¹) v₀,
          mumfordIdeal_mem_nonZeroDivisors f hm₀.ne_zero v₀⟩ :=
      mk0_congr f _ _ (mumfordIdeal_mul_leadingCoeff_inv f hu₀).symm
    _ = ClassGroup.mk0 ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hm.ne_zero v⟩ := heq

/-! ### Uniqueness (blueprint node `lem:mumford-exists`) -/

-- The norm of the principal generator of `(u₁,y-v₁)·(u₂,y-v₂)^★` generates `(u₁·u₂)`.
private lemma span_norm_eq_span_mul {h : HypRing K f} {u₁ v₁ u₂ v₂ : K[X]}
    (hu₁0 : u₁ ≠ 0) (hu₂0 : u₂ ≠ 0) (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f)
    (hh0 : h ≠ 0)
    (hh : mumfordIdeal f u₁ v₁ * (mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f))
      = Ideal.span {h})
    (hh' : (mumfordIdeal f u₁ v₁).map (starRingEnd (HypRing K f)) * mumfordIdeal f u₂ v₂
      = Ideal.span {star h}) :
    Ideal.span ({Algebra.norm K[X] h} : Set K[X]) = Ideal.span {u₁ * u₂} := by
  have hsf : Squarefree f := Fact.out
  have hA : Ideal.span {algebraMap K[X] (HypRing K f) (Algebra.norm K[X] h)}
      = Ideal.span {algebraMap K[X] (HypRing K f) (u₁ * u₂)} := by
    calc Ideal.span {algebraMap K[X] (HypRing K f) (Algebra.norm K[X] h)}
        = Ideal.span {h * star h} := by rw [← HypRing.mul_star_eq_norm]
      _ = Ideal.span {h} * Ideal.span {star h} :=
          (Ideal.span_singleton_mul_span_singleton _ _).symm
      _ = (mumfordIdeal f u₁ v₁ * (mumfordIdeal f u₁ v₁).map (starRingEnd (HypRing K f)))
          * (mumfordIdeal f u₂ v₂ * (mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f)))
          := by rw [← hh, ← hh']; ring
      _ = Ideal.span {algebraMap K[X] (HypRing K f) u₁}
          * Ideal.span {algebraMap K[X] (HypRing K f) u₂} := by
          rw [mumfordIdeal_mul_map_star f hsf two_ne_zero hd₁,
            mumfordIdeal_mul_map_star f hsf two_ne_zero hd₂]
      _ = Ideal.span {algebraMap K[X] (HypRing K f) (u₁ * u₂)} := by
          rw [Ideal.span_singleton_mul_span_singleton, ← map_mul]
  have hN0 : Algebra.norm K[X] h ≠ 0 := by
    intro h0
    have hns := HypRing.mul_star_eq_norm f h
    rw [h0, map_zero, mul_eq_zero] at hns
    rcases hns with hz | hz
    · exact hh0 hz
    · exact hh0 (by simpa using congrArg star hz)
  calc Ideal.span ({Algebra.norm K[X] h} : Set K[X])
      = (Ideal.span {algebraMap K[X] (HypRing K f) (Algebra.norm K[X] h)}).comap
          (algebraMap K[X] (HypRing K f)) :=
        (comap_span_singleton_algebraMap f hN0).symm
    _ = (Ideal.span {algebraMap K[X] (HypRing K f) (u₁ * u₂)}).comap
          (algebraMap K[X] (HypRing K f)) := by rw [hA]
    _ = Ideal.span {u₁ * u₂} :=
        comap_span_singleton_algebraMap f (mul_ne_zero hu₁0 hu₂0)

/-- Uniqueness of reduced Mumford representatives: two reduced Mumford ideals in the
same class of `J(K)` have the same data. -/
theorem mumfordIdeal_reduced_unique {u₁ v₁ u₂ v₂ : K[X]}
    (hm₁ : u₁.Monic) (hm₂ : u₂.Monic)
    (hv₁ : v₁.degree < u₁.degree) (hv₂ : v₂.degree < u₂.degree)
    (hg₁ : 2 * u₁.natDegree < f.natDegree) (hg₂ : 2 * u₂.natDegree < f.natDegree)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f)
    (hcl : ClassGroup.mk0
        ⟨mumfordIdeal f u₁ v₁, mumfordIdeal_mem_nonZeroDivisors f hm₁.ne_zero v₁⟩
      = ClassGroup.mk0
        ⟨mumfordIdeal f u₂ v₂, mumfordIdeal_mem_nonZeroDivisors f hm₂.ne_zero v₂⟩) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  have hmem₁ := mumfordIdeal_mem_nonZeroDivisors f hm₁.ne_zero v₁
  have hmem₂ := mumfordIdeal_mem_nonZeroDivisors f hm₂.ne_zero v₂
  -- the connecting ideal is principal and integral
  have hprin : (mumfordIdeal f u₁ v₁
      * (mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f))).IsPrincipal := by
    refine (ClassGroup.mk0_eq_one_iff
      (Submonoid.mul_mem _ hmem₁ (map_star_mem_nonZeroDivisors f hmem₂))).mp ?_
    rw [show (⟨_ * _, Submonoid.mul_mem _ hmem₁ (map_star_mem_nonZeroDivisors f hmem₂)⟩
        : (Ideal (HypRing K f))⁰)
      = ⟨mumfordIdeal f u₁ v₁, hmem₁⟩
        * ⟨(mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f)),
            map_star_mem_nonZeroDivisors f hmem₂⟩ from rfl, map_mul,
      classGroup_mk0_mumfordIdeal_map_star f hd₂ hm₂.ne_zero hmem₂, hcl, mul_inv_cancel]
  obtain ⟨h, hh₀⟩ := Submodule.IsPrincipal.principal
    (mumfordIdeal f u₁ v₁ * (mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f)))
  have hh : mumfordIdeal f u₁ v₁ * (mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f))
      = Ideal.span {h} := hh₀
  clear hh₀
  have hu₁0 := hm₁.ne_zero
  have hu₂0 := hm₂.ne_zero
  -- h is nonzero
  have hh0 : h ≠ 0 := by
    rintro rfl
    refine mem_nonZeroDivisors_iff_ne_zero.mp
      (Submonoid.mul_mem _ hmem₁ (map_star_mem_nonZeroDivisors f hmem₂)) ?_
    rw [hh]
    simp
  -- the conjugate equation
  have hh' : (mumfordIdeal f u₁ v₁).map (starRingEnd (HypRing K f)) * mumfordIdeal f u₂ v₂
      = Ideal.span {star h} := by
    have hmap := congrArg (Ideal.map (starRingEnd (HypRing K f))) hh
    rwa [Ideal.map_mul, map_star_map_star, map_star_span_singleton] at hmap
  -- the norm of h generates (u₁·u₂)
  have hnorm := span_norm_eq_span_mul f hu₁0 hu₂0 hd₁ hd₂ hh0 hh hh'
  -- degrees force h ∈ K[x]
  obtain ⟨hha, hstar⟩ := eq_algebraMap_re_of_span_norm f hu₁0 hu₂0 hg₁ hg₂ hnorm
  have hre0 : h.re ≠ 0 := by
    intro h0
    rw [hha, h0, map_zero] at hh0
    exact hh0 rfl
  -- two rescaled equations, and their traces on K[x]
  have heq1 : Ideal.span {algebraMap K[X] (HypRing K f) u₂} * mumfordIdeal f u₁ v₁
      = Ideal.span {algebraMap K[X] (HypRing K f) h.re} * mumfordIdeal f u₂ v₂ := by
    rw [← hha]
    exact span_mul_mumfordIdeal_eq f Fact.out two_ne_zero hd₂ hh
  have heq2 : Ideal.span {algebraMap K[X] (HypRing K f) u₁} * mumfordIdeal f u₂ v₂
      = Ideal.span {algebraMap K[X] (HypRing K f) h.re} * mumfordIdeal f u₁ v₁ := by
    rw [← hha, ← hstar]
    exact span_mul_mumfordIdeal_eq f Fact.out two_ne_zero hd₁ (by rw [mul_comm]; exact hh')
  -- take traces
  have hcm1 := comap_span_mul_mumfordIdeal f hu₂0 hre0 hd₁ hd₂ heq1
  have hcm2 := comap_span_mul_mumfordIdeal f hu₁0 hre0 hd₂ hd₁ heq2
  -- u₁ and u₂ are both associated to h.re, hence equal (monic)
  obtain ⟨c₁, hc₁⟩ := Ideal.span_singleton_eq_span_singleton.mp hcm1
  obtain ⟨c₂, hc₂⟩ := Ideal.span_singleton_eq_span_singleton.mp hcm2
  have ha₁ : u₁ * c₁ = h.re := mul_left_cancel₀ hu₂0 (by linear_combination hc₁)
  have ha₂ : u₂ * c₂ = h.re := mul_left_cancel₀ hu₁0 (by linear_combination hc₂)
  have hu12 : u₁ = u₂ := by
    refine eq_of_monic_of_associated hm₁ hm₂ ⟨c₁ * c₂⁻¹, ?_⟩
    rw [Units.val_mul, ← mul_assoc, ha₁, ← ha₂]
    exact Units.mul_inv_cancel_right _ _
  subst hu12
  -- the ideals coincide
  have hspan_a : Ideal.span {algebraMap K[X] (HypRing K f) h.re}
      = Ideal.span {algebraMap K[X] (HypRing K f) u₁} := by
    refine Ideal.span_singleton_eq_span_singleton.mpr ?_
    exact Associated.map (algebraMap K[X] (HypRing K f) : K[X] →* HypRing K f) ⟨c₁, ha₁⟩ |>.symm
  rw [hspan_a] at heq1
  have hIeq : mumfordIdeal f u₁ v₁ = mumfordIdeal f u₁ v₂ := by
    have hne : Ideal.span {algebraMap K[X] (HypRing K f) u₁} ≠ 0 :=
      span_singleton_algebraMap_ne_zero f hu₁0
    exact mul_left_cancel₀ hne heq1
  -- and finally the v's
  have hyv : HypRing.y f - algebraMap K[X] (HypRing K f) v₁ ∈ mumfordIdeal f u₁ v₂ :=
    hIeq ▸ y_sub_mem_mumfordIdeal f u₁ v₁
  rw [mem_mumfordIdeal_iff f hd₂] at hyv
  have hdvd' : u₁ ∣ v₂ - v₁ := by
    have h' : u₁ ∣ -v₁ + v₂ := by simpa using hyv
    rwa [neg_add_eq_sub] at h'
  have hdiff : v₂ - v₁ = 0 := eq_zero_of_dvd_of_degree_lt hdvd'
    (lt_of_le_of_lt (degree_sub_le v₂ v₁) (max_lt hv₂ hv₁))
  exact ⟨rfl, (sub_eq_zero.mp hdiff).symm⟩

end ChabautyColeman

end
