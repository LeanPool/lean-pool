/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.IntegralClosure
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Mumford ideals

The Mumford ideal `ChabautyColeman.mumfordIdeal f u v = (u, y - v)` of the coordinate
ring, for polynomials `u, v ∈ K[x]`; point ideals are the special case
`u = x - x₀, v = y₀` (see `ChabautyColeman.pointIdeal_eq_mumfordIdeal`).

Whenever `u ∣ v² - f`, evaluation `p + q·y ↦ p + q·v mod u` is a ring homomorphism
`ChabautyColeman.mumfordHom : A_K → K[x]/(u)`; it is surjective with kernel `(u, y - v)`,
so the quotient of `A_K` by a Mumford ideal is `K[x]/(u)`
(`ChabautyColeman.mumfordQuotEquiv`).

We also prove the norm identity `(u, y - v)·(u, y + v) = (u)` for `u ∣ v² - f` with
`f` squarefree and `2 ∈ K^×` (`ChabautyColeman.mumfordIdeal_mul_map_star`), where
`(u, y + v)` is the image of `(u, y - v)` under the involution
(`ChabautyColeman.map_star_mumfordIdeal`). The proof needs no factorization into primes:
the reverse inclusion is a Bézout identity for `(u, 2v, w)` with `w = (v² - f)/u`, a
common prime `π` of which would force `π² ∣ f`.

Blueprint nodes: `def:mumford-ideal`, `lem:mumford-norm`; the existence and uniqueness of
reduced representatives (`lem:mumford-exists`) are built on this in
`LeanPool.HyperellipticCurves.Curve.MumfordReduction`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

open QuadraticAlgebra Ideal

variable {K : Type*} [Field K] (f : K[X])

/-- The Mumford ideal `(u, y - v)` of the coordinate ring attached to a pair of
polynomials `u, v`. -/
noncomputable def mumfordIdeal (u v : K[X]) : Ideal (HypRing K f) :=
  Ideal.span {algebraMap K[X] _ u, HypRing.y f - algebraMap K[X] _ v}

theorem mumfordIdeal_eq_span (u v : K[X]) :
    mumfordIdeal f u v = Ideal.span {algebraMap K[X] _ u, HypRing.y f - algebraMap K[X] _ v} :=
  rfl

theorem algebraMap_mem_mumfordIdeal (u v : K[X]) :
    algebraMap K[X] (HypRing K f) u ∈ mumfordIdeal f u v :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem y_sub_mem_mumfordIdeal (u v : K[X]) :
    HypRing.y f - algebraMap K[X] (HypRing K f) v ∈ mumfordIdeal f u v :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- The Mumford ideal with trivial support is the unit ideal. -/
theorem mumfordIdeal_one (v : K[X]) : mumfordIdeal f 1 v = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← map_one (algebraMap K[X] (HypRing K f))]
  exact algebraMap_mem_mumfordIdeal f 1 v

/-- The Mumford ideal only depends on the `v`-part modulo the support. -/
theorem mumfordIdeal_eq_of_dvd_sub {u v v' : K[X]} (h : u ∣ v - v') :
    mumfordIdeal f u v = mumfordIdeal f u v' := by
  obtain ⟨c, hc⟩ := h
  have hgen : HypRing.y f - algebraMap K[X] (HypRing K f) v
      = (HypRing.y f - algebraMap K[X] (HypRing K f) v')
        + (-(algebraMap K[X] (HypRing K f) c)) * algebraMap K[X] (HypRing K f) u := by
    rw [show v = v' + u * c by linear_combination hc, map_add, map_mul]
    ring
  rw [mumfordIdeal_eq_span, mumfordIdeal_eq_span, hgen]
  exact Ideal.span_pair_add_mul_left (algebraMap K[X] (HypRing K f) u)
    (HypRing.y f - algebraMap K[X] (HypRing K f) v') (-(algebraMap K[X] (HypRing K f) c))

theorem mumfordIdeal_ne_bot {u : K[X]} (hu : u ≠ 0) (v : K[X]) : mumfordIdeal f u v ≠ ⊥ := by
  intro h
  have hx := algebraMap_mem_mumfordIdeal f u v
  rw [h, Ideal.mem_bot] at hx
  exact hu ((map_eq_zero_iff _ QuadraticAlgebra.algebraMap_injective).mp hx)

/-- The `≠ 0` form of `ChabautyColeman.mumfordIdeal_ne_bot`, in the currency the
`nonZeroDivisors` consumers spend. -/
theorem mumfordIdeal_ne_zero {u : K[X]} (hu : u ≠ 0) (v : K[X]) : mumfordIdeal f u v ≠ 0 := by
  simpa [Submodule.zero_eq_bot] using mumfordIdeal_ne_bot f hu v

/-- A nonzero polynomial spans a nonzero ideal of the coordinate ring. -/
theorem span_singleton_algebraMap_ne_zero {c : K[X]} (hc : c ≠ 0) :
    Ideal.span {algebraMap K[X] (HypRing K f) c} ≠ 0 := by
  rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot,
    map_eq_zero_iff _ QuadraticAlgebra.algebraMap_injective]
  exact hc

variable {u v : K[X]}

/-- Evaluation `p + q·y ↦ p + q·v mod u` of the coordinate ring in `K[x]/(u)`;
this is a ring homomorphism whenever `u ∣ v² - f`, and its kernel is the Mumford
ideal `(u, y - v)`. -/
noncomputable def mumfordHom (h : u ∣ v ^ 2 - f) :
    HypRing K f →+* K[X] ⧸ Ideal.span {u} where
  toFun z := Ideal.Quotient.mk _ (z.re + z.im * v)
  map_one' := by simp
  map_zero' := by simp
  map_add' z w := by
    rw [← map_add]
    exact congrArg _ (by simp; ring)
  map_mul' z w := by
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_span_singleton]
    rw [show (z * w).re + (z * w).im * v - (z.re + z.im * v) * (w.re + w.im * v)
      = z.im * w.im * (f - v ^ 2) by simp; ring]
    have h' : u ∣ f - v ^ 2 := by rwa [← neg_sub, dvd_neg]
    exact h'.mul_left _

theorem mumfordHom_apply (h : u ∣ v ^ 2 - f) (z : HypRing K f) :
    mumfordHom f h z = Ideal.Quotient.mk _ (z.re + z.im * v) := rfl

theorem mumfordHom_surjective (h : u ∣ v ^ 2 - f) : Function.Surjective (mumfordHom f h) :=
  fun p ↦ by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective p
    exact ⟨algebraMap K[X] _ q, by simp [mumfordHom_apply]⟩

theorem ker_mumfordHom (h : u ∣ v ^ 2 - f) :
    RingHom.ker (mumfordHom f h) = mumfordIdeal f u v := by
  refine le_antisymm (fun z hz ↦ ?_) ?_
  · rw [RingHom.mem_ker, mumfordHom_apply, Ideal.Quotient.eq_zero_iff_mem,
      mem_span_singleton] at hz
    obtain ⟨c, hc⟩ := hz
    have hdec : z = algebraMap K[X] _ u * algebraMap K[X] _ c
        + algebraMap K[X] _ z.im * (HypRing.y f - algebraMap K[X] _ v) := by
      ext <;> simp [← hc]
    rw [hdec]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (algebraMap_mem_mumfordIdeal f u v))
      (Ideal.mul_mem_left _ _ (y_sub_mem_mumfordIdeal f u v))
  · rw [mumfordIdeal_eq_span, Ideal.span_le]
    rintro z (rfl | rfl) <;>
      simp [SetLike.mem_coe, RingHom.mem_ker, mumfordHom_apply]

/-- The quotient by a Mumford ideal is `K[x]/(u)`. -/
noncomputable def mumfordQuotEquiv (h : u ∣ v ^ 2 - f) :
    (HypRing K f ⧸ mumfordIdeal f u v) ≃+* K[X] ⧸ Ideal.span {u} :=
  (Ideal.quotEquivOfEq (ker_mumfordHom f h).symm).trans
    (RingHom.quotientKerEquivOfSurjective (mumfordHom_surjective f h))

/-! ### The norm identity (blueprint node `lem:mumford-norm`) -/

variable (u v) in
/-- The involution maps the Mumford ideal `(u, y - v)` to `(u, y + v)`. -/
theorem map_star_mumfordIdeal :
    (mumfordIdeal f u v).map (starRingEnd (HypRing K f)) = mumfordIdeal f u (-v) := by
  rw [mumfordIdeal_eq_span, mumfordIdeal_eq_span, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton]
  have h1 : starRingEnd (HypRing K f) (algebraMap K[X] _ u) = algebraMap K[X] _ u :=
    QuadraticAlgebra.star_algebraMap u
  have h2 : starRingEnd (HypRing K f) (HypRing.y f - algebraMap K[X] _ v)
      = -(HypRing.y f - algebraMap K[X] _ (-v)) := by
    ext <;> simp [starRingEnd_apply]
  rw [h1, h2, Ideal.span_pair_neg]

private lemma isUnit_two (h2 : (2 : K) ≠ 0) : IsUnit (2 : K[X]) := by
  have h : (2 : K[X]) = C 2 := by rw [map_ofNat]
  rw [h, Polynomial.isUnit_C]
  exact h2.isUnit

-- Bézout for the triple `(u, 2v, w)`: no common prime, by squarefreeness of `f`
private lemma span_triple_eq_top (hsf : Squarefree f) (h2 : (2 : K) ≠ 0) {w : K[X]}
    (hw : v ^ 2 - f = u * w) :
    Ideal.span {u, 2 * v, w} = ⊤ := by
  by_contra hne
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨π, hM⟩ := IsPrincipalIdealRing.principal M
  rw [hM] at hMmax hle
  have hu : π ∣ u := mem_span_singleton.mp (hle (subset_span (by simp)))
  have hv2 : π ∣ 2 * v := mem_span_singleton.mp (hle (subset_span (by simp)))
  have hwd : π ∣ w := mem_span_singleton.mp (hle (subset_span (by simp)))
  rcases eq_or_ne π 0 with rfl | hπ0
  · rw [zero_dvd_iff] at hu hv2 hwd
    have hv0 : v = 0 := (mul_eq_zero.mp hv2).resolve_left (isUnit_two h2).ne_zero
    refine hsf.ne_zero ?_
    rw [hu, hv0] at hw
    linear_combination -hw
  · have hπ : Prime π := (span_singleton_prime hπ0).mp hMmax.isPrime
    have hv : π ∣ v := (hπ.dvd_mul.mp hv2).resolve_left
      fun hd ↦ hπ.not_isUnit (isUnit_of_dvd_unit hd (isUnit_two h2))
    have hff : π * π ∣ f := by
      have h := dvd_sub (mul_dvd_mul hv hv) (mul_dvd_mul hu hwd)
      rwa [← sq v, ← hw, sub_sub_cancel] at h
    exact hπ.not_isUnit (hsf π hff)

/-- The norm identity for Mumford ideals: for `u ∣ v² - f` with `f` squarefree
(and `2 ∈ K^×`), `(u, y - v) · (u, y + v) = (u)`. -/
theorem mumfordIdeal_mul_map_star (hsf : Squarefree f) (h2 : (2 : K) ≠ 0)
    (h : u ∣ v ^ 2 - f) :
    mumfordIdeal f u v * (mumfordIdeal f u v).map (starRingEnd (HypRing K f))
      = Ideal.span {algebraMap K[X] (HypRing K f) u} := by
  obtain ⟨w, hw⟩ := h
  rw [map_star_mumfordIdeal]
  have hyy : (HypRing.y f - algebraMap K[X] (HypRing K f) v)
      * (HypRing.y f - algebraMap K[X] (HypRing K f) (-v))
      = algebraMap K[X] (HypRing K f) (f - v ^ 2) := by
    rw [map_neg, map_sub, map_pow]
    linear_combination HypRing.y_sq f
  refine le_antisymm ?_ ?_
  · -- each generator product is divisible by `u`
    rw [mumfordIdeal_eq_span, mumfordIdeal_eq_span, Ideal.span_mul_span]
    refine Ideal.span_le.mpr ?_
    rintro z ⟨p, hp, q, hq, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    refine Ideal.mem_span_singleton.mpr ?_
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
    · rw [hyy]
      refine (map_dvd _ ?_ : _ ∣ algebraMap K[X] (HypRing K f) (f - v ^ 2))
      exact ⟨-w, by linear_combination -hw⟩
  · -- `u` is a combination of the generator products, via Bézout for `(u, 2v, w)`
    set A := HypRing K f
    set I := mumfordIdeal f u v
    set J := mumfordIdeal f u (-v)
    have hm1 : algebraMap K[X] A (u * u) ∈ I * J := by
      rw [map_mul]
      exact Ideal.mul_mem_mul (algebraMap_mem_mumfordIdeal f u v)
        (algebraMap_mem_mumfordIdeal f u (-v))
    have hm2 : algebraMap K[X] A (u * (2 * v)) ∈ I * J := by
      have hcomb : algebraMap K[X] A (u * (2 * v))
          = algebraMap K[X] A u * (HypRing.y f - algebraMap K[X] A (-v))
            - (HypRing.y f - algebraMap K[X] A v) * algebraMap K[X] A u := by
        rw [map_neg, show (2 * v : K[X]) = v + v by ring, map_mul, map_add]
        ring
      rw [hcomb]
      exact sub_mem
        (Ideal.mul_mem_mul (algebraMap_mem_mumfordIdeal f u v) (y_sub_mem_mumfordIdeal f u (-v)))
        (Ideal.mul_mem_mul (y_sub_mem_mumfordIdeal f u v) (algebraMap_mem_mumfordIdeal f u (-v)))
    have hm3 : algebraMap K[X] A (u * w) ∈ I * J := by
      have hcomb : algebraMap K[X] A (u * w)
          = -((HypRing.y f - algebraMap K[X] A v) * (HypRing.y f - algebraMap K[X] A (-v))) := by
        rw [hyy, ← map_neg]
        exact congrArg _ (by linear_combination -hw)
      rw [hcomb]
      exact neg_mem (Ideal.mul_mem_mul (y_sub_mem_mumfordIdeal f u v)
        (y_sub_mem_mumfordIdeal f u (-v)))
    have key (r : K[X]) (hr : algebraMap K[X] A (u * r) ∈ I * J) :
        r • algebraMap K[X] A u ∈ (I * J).restrictScalars K[X] := by
      rwa [Algebra.smul_def, ← map_mul, mul_comm r u]
    rw [Ideal.span_le, Set.singleton_subset_iff]
    refine Submodule.mem_of_span_top_of_smul_mem ((I * J).restrictScalars K[X]) {u, 2 * v, w}
      (span_triple_eq_top f hsf h2 hw) _ ?_
    intro ⟨r, hr⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · exact key _ hm1
    · exact key _ hm2
    · exact key _ hm3

/-- Rescaling one Mumford ideal by the other's `u` is multiplying the other by a generator of
the connecting ideal — the norm identity `(u₂, y-v₂)·(u₂, y+v₂) = (u₂)` moved across the
product. -/
theorem span_mul_mumfordIdeal_eq (hsf : Squarefree f) (h2 : (2 : K) ≠ 0) {u₁ v₁ u₂ v₂ : K[X]}
    {h : HypRing K f} (hd₂ : u₂ ∣ v₂ ^ 2 - f)
    (hh : mumfordIdeal f u₁ v₁ * (mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f))
      = Ideal.span {h}) :
    Ideal.span {algebraMap K[X] (HypRing K f) u₂} * mumfordIdeal f u₁ v₁
      = Ideal.span {h} * mumfordIdeal f u₂ v₂ :=
  calc Ideal.span {algebraMap K[X] (HypRing K f) u₂} * mumfordIdeal f u₁ v₁
      = (mumfordIdeal f u₂ v₂ * (mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f)))
        * mumfordIdeal f u₁ v₁ := by rw [mumfordIdeal_mul_map_star f hsf h2 hd₂]
    _ = (mumfordIdeal f u₁ v₁ * (mumfordIdeal f u₂ v₂).map (starRingEnd (HypRing K f)))
        * mumfordIdeal f u₂ v₂ := by ring
    _ = Ideal.span {h} * mumfordIdeal f u₂ v₂ := by rw [hh]

/-! ### The divisor of `y - v` (blueprint node `lem:mumford-divisor-y`) -/

/-- The divisor of `y - v`: for `v² - f = u·w` (`f` squarefree, `2 ∈ K^×`),
`(u, y - v) · (w, y - v) = (y - v)`. This is the engine of Cantor's reduction step. -/
theorem mumfordIdeal_mul_cofactor {w : K[X]} (hsf : Squarefree f) (h2 : (2 : K) ≠ 0)
    (hw : v ^ 2 - f = u * w) :
    mumfordIdeal f u v * mumfordIdeal f w v
      = Ideal.span {HypRing.y f - algebraMap K[X] (HypRing K f) v} := by
  have hyy : (HypRing.y f - algebraMap K[X] (HypRing K f) v)
      * (HypRing.y f + algebraMap K[X] (HypRing K f) v)
      = algebraMap K[X] (HypRing K f) (f - v ^ 2) := by
    rw [map_sub, map_pow]
    linear_combination HypRing.y_sq f
  refine le_antisymm ?_ ?_
  · -- each generator product is divisible by y - v
    rw [mumfordIdeal_eq_span, mumfordIdeal_eq_span, Ideal.span_mul_span]
    refine Ideal.span_le.mpr ?_
    rintro z ⟨p, hp, q, hq, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    refine Ideal.mem_span_singleton.mpr ?_
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · -- u·w = -(y - v)(y + v)
      refine ⟨-(HypRing.y f + algebraMap K[X] _ v), ?_⟩
      rw [← map_mul, show u * w = -(f - v ^ 2) by linear_combination -hw, map_neg, ← hyy]
      ring
    · exact dvd_mul_left _ _
    · exact dvd_mul_right _ _
    · exact dvd_mul_right _ _
  · -- y - v is a combination of the generator products, via Bézout for (u, 2v, w)
    set A := HypRing K f
    set yv := HypRing.y f - algebraMap K[X] A v with hyv
    have hm1 : yv * algebraMap K[X] A u ∈ mumfordIdeal f u v * mumfordIdeal f w v :=
      mul_comm yv (algebraMap K[X] A u) ▸
        Ideal.mul_mem_mul (algebraMap_mem_mumfordIdeal f u v) (y_sub_mem_mumfordIdeal f w v)
    have hm2 : yv * algebraMap K[X] A w ∈ mumfordIdeal f u v * mumfordIdeal f w v :=
      Ideal.mul_mem_mul (y_sub_mem_mumfordIdeal f u v) (algebraMap_mem_mumfordIdeal f w v)
    have hm3 : yv * algebraMap K[X] A (2 * v) ∈ mumfordIdeal f u v * mumfordIdeal f w v := by
      have hcomb : yv * algebraMap K[X] A (2 * v)
          = -(algebraMap K[X] A u * algebraMap K[X] A w) - yv * yv := by
        rw [← map_mul, show u * w = -(f - v ^ 2) by linear_combination -hw, map_neg,
          neg_neg, ← hyy, hyv, show (2 * v : K[X]) = v + v by ring, map_add]
        ring
      rw [hcomb]
      exact sub_mem (neg_mem (Ideal.mul_mem_mul (algebraMap_mem_mumfordIdeal f u v)
          (algebraMap_mem_mumfordIdeal f w v)))
        (Ideal.mul_mem_mul (y_sub_mem_mumfordIdeal f u v) (y_sub_mem_mumfordIdeal f w v))
    have key (r : K[X]) (hr : yv * algebraMap K[X] A r
        ∈ mumfordIdeal f u v * mumfordIdeal f w v) :
        r • yv ∈ (mumfordIdeal f u v * mumfordIdeal f w v).restrictScalars K[X] := by
      rwa [Algebra.smul_def, mul_comm (algebraMap K[X] A r) yv]
    rw [Ideal.span_le, Set.singleton_subset_iff]
    refine Submodule.mem_of_span_top_of_smul_mem
      ((mumfordIdeal f u v * mumfordIdeal f w v).restrictScalars K[X]) {u, 2 * v, w}
      (span_triple_eq_top f hsf h2 hw) _ ?_
    intro ⟨r, hr⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · exact key _ hm1
    · exact key _ hm3
    · exact key _ hm2

/-! ### Semi-reduction (blueprint node `lem:mumford-semireduced`)

Every nonzero ideal of `A_K` is a polynomial multiple of a Mumford ideal; the proof is a
Hermite-normal-form argument over the PID `K[x]` (no factorization into primes): with
`c` a generator of `im(𝔞)` and `a` a generator of `𝔞 ∩ K[x]`, one has
`𝔞 = (a, z₀) = (c)·(u, y - v)` for `a = c·u` and a lift `z₀ = c·(y - v)`, and
ideal-closedness under multiplication by `y` yields `u ∣ v² - f`.
-/

section SemiReduction

variable [Fact (Odd f.natDegree)]

/-- Structure theorem (semi-reduction): every nonzero ideal of the coordinate ring is a
polynomial multiple of a Mumford ideal. -/
theorem exists_span_singleton_mul_mumfordIdeal (𝔞 : Ideal (HypRing K f)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ c u v : K[X], c ≠ 0 ∧ u ≠ 0 ∧ u ∣ v ^ 2 - f ∧
      𝔞 = Ideal.span {algebraMap K[X] (HypRing K f) c} * mumfordIdeal f u v := by
  -- the image of 𝔞 under `im` and the trace of 𝔞 on K[x] are principal
  obtain ⟨c, hcspan⟩ := Submodule.IsPrincipal.principal
    (Submodule.map (QuadraticAlgebra.imₗ f 0) (Submodule.restrictScalars K[X] 𝔞) : Ideal K[X])
  obtain ⟨a, haspan⟩ :=
    Submodule.IsPrincipal.principal (Ideal.comap (algebraMap K[X] (HypRing K f)) 𝔞)
  have hIm (z : HypRing K f) (hz : z ∈ 𝔞) : c ∣ z.im := by
    have hmem : z.im ∈ Submodule.map (QuadraticAlgebra.imₗ f 0)
      (Submodule.restrictScalars K[X] 𝔞) := ⟨z, hz, rfl⟩
    rw [hcspan] at hmem
    exact Ideal.mem_span_singleton.mp hmem
  have hRe (p : K[X]) (hp : algebraMap K[X] (HypRing K f) p ∈ 𝔞) : a ∣ p := by
    have hmem : p ∈ Ideal.comap (algebraMap K[X] (HypRing K f)) 𝔞 := Ideal.mem_comap.mpr hp
    rw [haspan] at hmem
    exact Ideal.mem_span_singleton.mp hmem
  obtain ⟨z₀, hz₀mem, hz₀im⟩ : ∃ z₀ ∈ 𝔞, z₀.im = c := by
    have hmem : c ∈ Submodule.map (QuadraticAlgebra.imₗ f 0)
        (Submodule.restrictScalars K[X] 𝔞) := by
      rw [hcspan]
      exact Ideal.subset_span rfl
    exact hmem
  have hAmem : algebraMap K[X] (HypRing K f) a ∈ 𝔞 := by
    have hmem : a ∈ Ideal.comap (algebraMap K[X] (HypRing K f)) 𝔞 := by
      rw [haspan]
      exact Ideal.subset_span rfl
    exact Ideal.mem_comap.mp hmem
  -- im and re of y·z
  have him_y (z : HypRing K f) : (HypRing.y f * z).im = z.re := by simp
  have hre_y (z : HypRing K f) : (HypRing.y f * z).re = f * z.im := by simp
  -- c divides z₀.re and a
  obtain ⟨v', hv'⟩ : c ∣ z₀.re := him_y z₀ ▸ hIm _ (𝔞.mul_mem_left _ hz₀mem)
  obtain ⟨u, hu⟩ : c ∣ a := by
    have h := hIm _ (𝔞.mul_mem_left (HypRing.y f) hAmem)
    rwa [him_y, QuadraticAlgebra.re_algebraMap] at h
  -- c ≠ 0
  obtain ⟨z₁, hz₁mem, hz₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine hz₁ ?_
    have h1 : z₁.im = 0 := zero_dvd_iff.mp (hIm _ hz₁mem)
    have h2 : z₁.re = 0 := by
      have h := zero_dvd_iff.mp (hIm _ (𝔞.mul_mem_left (HypRing.y f) hz₁mem))
      rwa [him_y] at h
    simp [QuadraticAlgebra.ext_iff, h1, h2]
  -- a ≠ 0, hence u ≠ 0
  have ha0 : a ≠ 0 := by
    have hnorm0 : Algebra.norm K[X] z₁ ≠ 0 := fun h0 ↦ by
      have h := HypRing.mul_star_eq_norm f z₁
      rw [h0, map_zero, mul_eq_zero] at h
      rcases h with h | h
      · exact hz₁ h
      · exact hz₁ (by simpa using congrArg star h)
    refine ne_zero_of_dvd_ne_zero hnorm0 (hRe _ ?_)
    rw [← HypRing.mul_star_eq_norm]
    exact 𝔞.mul_mem_right _ hz₁mem
  have hu0 : u ≠ 0 := right_ne_zero_of_mul (hu ▸ ha0)
  -- every element of 𝔞 is a K[x]-combination of `a` and `z₀`
  have hdecomp (z : HypRing K f) (hz : z ∈ 𝔞) : ∃ p q : K[X],
      z = algebraMap K[X] _ p * algebraMap K[X] _ a + algebraMap K[X] _ q * z₀ := by
    obtain ⟨q, hq⟩ := hIm z hz
    have hwmem : z - algebraMap K[X] _ q * z₀ ∈ 𝔞 :=
      sub_mem hz (𝔞.mul_mem_left _ hz₀mem)
    have hwim : (z - algebraMap K[X] _ q * z₀).im = 0 := by simp [hq, hz₀im, mul_comm]
    have hweq := QuadraticAlgebra.eq_algebraMap_re hwim
    obtain ⟨p, hp⟩ := hRe _ (hweq ▸ hwmem)
    refine ⟨p, q, ?_⟩
    rw [hp, map_mul] at hweq
    linear_combination hweq
  -- the Mumford divisibility condition
  obtain ⟨p, q, hpq⟩ := hdecomp _ (𝔞.mul_mem_left (HypRing.y f) hz₀mem)
  have him_eq := congrArg QuadraticAlgebra.im hpq
  have hre_eq := congrArg QuadraticAlgebra.re hpq
  simp only [him_y, hre_y, QuadraticAlgebra.im_add, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_algebraMap,
    QuadraticAlgebra.im_algebraMap, Algebra.algebraMap_self, RingHom.id_apply, mul_zero,
    zero_mul, add_zero, zero_add] at him_eq hre_eq
  have hq_eq : q = v' := by
    apply mul_left_cancel₀ hc0
    rw [hv', hz₀im] at him_eq
    linear_combination -him_eq
  have hdvd : u ∣ v' ^ 2 - f := by
    refine ⟨-p, ?_⟩
    rw [hz₀im, hu, hv', hq_eq] at hre_eq
    have h2 : c * (v' ^ 2 - f) = c * (u * -p) := by linear_combination -hre_eq
    exact mul_left_cancel₀ hc0 h2
  refine ⟨c, u, -v', hc0, hu0, by simpa using hdvd, ?_⟩
  -- both sides are spanned by `algebraMap a` and `z₀`
  have hgen2 : algebraMap K[X] (HypRing K f) c
      * (HypRing.y f - algebraMap K[X] _ (-v')) = z₀ := by
    ext
    · simp [hv']
    · simp [hz₀im]
  have hRHS : Ideal.span {algebraMap K[X] (HypRing K f) c} * mumfordIdeal f u (-v')
      = Ideal.span {algebraMap K[X] (HypRing K f) a, z₀} := by
    rw [mumfordIdeal_eq_span, Ideal.span_mul_span, Set.singleton_mul, Set.image_insert_eq,
      Set.image_singleton, ← map_mul, ← hu, hgen2]
  rw [hRHS]
  refine le_antisymm (fun z hz ↦ ?_) ?_
  · obtain ⟨p', q', hpq'⟩ := hdecomp z hz
    rw [Ideal.mem_span_pair]
    exact ⟨algebraMap K[X] _ p', algebraMap K[X] _ q', hpq'.symm⟩
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact hAmem
    · exact hz₀mem

end SemiReduction

end ChabautyColeman

end
