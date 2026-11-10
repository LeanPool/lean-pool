/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.BaseChange
public import LeanPool.HyperellipticCurves.Curve.PointValuation
public import LeanPool.HyperellipticCurves.Specialization.FiberSum

import LeanPool.HyperellipticCurves.ForMathlib.Multiplicity
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Target-flexible base change of the coordinate ring

For a field extension `K ⊆ L` and a polynomial `g` with `f.map (algebraMap K L) = g`,
`ChabautyColeman.HypRing.baseChangeTo` is base change of the coordinate ring `A_K → A_L` with
the index equation as an argument rather than as a definitional constraint — the form that
composes without casts (`LeanPool.HyperellipticCurves.Curve.BaseChange` has the rigid
`HypRing.baseChange`).

## Main statements

* `ChabautyColeman.HypRing.baseChangeTo` and its API: the two components, injectivity, and the
  values on `x` and `y`.
* `ChabautyColeman.pointIdeal_baseChangeTo`, `ChabautyColeman.evalHom_baseChangeTo`: point
  ideals and point evaluation transport.
* `ChabautyColeman.isIntegral_baseChangeTo`: `A_L` is integral over `A_K` when `L/K` is finite.
* `ChabautyColeman.exists_prime_dvd_of_prime_dvd_map`: every nonzero prime divisor of the
  extension of `I` divides the extension of some nonzero prime divisor of `I` — a divisor
  contraction, by that integrality.

Stability of the multiplicity of a rational point ideal under base change
(`ChabautyColeman.emultiplicity_pointIdeal_map_baseChangeTo`) is formalized in
`upstream HyperellipticCurves.Archive.BaseChangeEmult`; the main theorems do not depend on it.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### Target-flexible base change of the coordinate ring -/

section BaseChangeTo

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (f : K[X]) {g : L[X]}
  (hg : f.map (algebraMap K L) = g)

/-- Base change of the coordinate ring along `algebraMap K L`, with a prescribed (equal)
target polynomial — the target-index-flexible form of `HypRing.baseChange`. -/
noncomputable def HypRing.baseChangeTo : HypRing K f →+* HypRing L g :=
  QuadraticAlgebra.mapRingHomTo (Polynomial.mapRingHom (algebraMap K L)) hg (map_zero _)

@[simp]
theorem HypRing.re_baseChangeTo (z : HypRing K f) :
    (baseChangeTo f hg z).re = z.re.map (algebraMap K L) := rfl

@[simp]
theorem HypRing.im_baseChangeTo (z : HypRing K f) :
    (baseChangeTo f hg z).im = z.im.map (algebraMap K L) := rfl

theorem HypRing.baseChangeTo_injective : Function.Injective (HypRing.baseChangeTo f hg) :=
  QuadraticAlgebra.mapRingHomTo_injective
    (Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective) hg (map_zero _)

@[simp]
theorem HypRing.baseChangeTo_algebraMap_X :
    baseChangeTo f hg (algebraMap K[X] (HypRing K f) X) = algebraMap L[X] (HypRing L g) X := by
  ext <;> simp

@[simp]
theorem HypRing.baseChangeTo_y : baseChangeTo f hg (HypRing.y f) = HypRing.y g := by
  ext <;> simp [HypRing.y]

/-- Point ideals extend to point ideals under target-flexible base change. -/
theorem pointIdeal_baseChangeTo (x y : K) :
    (pointIdeal f x y).map (HypRing.baseChangeTo f hg)
      = pointIdeal g (algebraMap K L x) (algebraMap K L y) := by
  have h1 : HypRing.baseChangeTo f hg (algebraMap K[X] _ (X - C x))
      = algebraMap L[X] _ (X - C (algebraMap K L x)) := by
    ext <;> simp
  have h2 : HypRing.baseChangeTo f hg (HypRing.y f - algebraMap K _ y)
      = HypRing.y g - algebraMap L _ (algebraMap K L y) := by
    ext <;> simp [HypRing.y]
  rw [pointIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, h1, h2, pointIdeal]

/-- Base change is compatible with the evaluation homomorphisms of a point and of its image. -/
theorem evalHom_baseChangeTo {x y : K} (h : y ^ 2 = f.eval x)
    (hL : (algebraMap K L y) ^ 2 = g.eval (algebraMap K L x)) (z : HypRing K f) :
    evalHom hL (HypRing.baseChangeTo f hg z) = algebraMap K L (evalHom h z) := by
  rw [evalHom_apply, evalHom_apply, HypRing.re_baseChangeTo, HypRing.im_baseChangeTo,
    eval_map_apply, eval_map_apply, map_add, map_mul]

/-- The extension of a nonzero ideal is nonzero (base change is injective). -/
theorem map_baseChangeTo_ne_bot {I : Ideal (HypRing K f)} (hI : I ≠ ⊥) :
    I.map (HypRing.baseChangeTo f hg) ≠ ⊥ :=
  mt (Ideal.map_eq_bot_iff_of_injective (HypRing.baseChangeTo_injective f hg)).mp hI

end BaseChangeTo

/-! ### Integrality and divisor contraction under a finite base change -/

section Contraction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {f : K[X]} {g : L[X]}
  (hg : f.map (algebraMap K L) = g) [FiniteDimensional K L]

/-- If, over an `L[X]`-algebra `B` that is also an `A`-algebra, both `X` and every constant `C c`
map to elements integral over `A`, then the image of every polynomial `p` is integral over `A`. -/
private theorem isIntegral_algebraMap_polynomial {A L B : Type*} [CommRing A] [Field L]
    [CommRing B] [Algebra A B] [Algebra L[X] B]
    (hC : ∀ c : L, IsIntegral A (algebraMap L[X] B (C c)))
    (hX : IsIntegral A (algebraMap L[X] B X)) (p : L[X]) :
    IsIntegral A (algebraMap L[X] B p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n c => rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]; exact (hC c).mul (hX.pow n)

/-- When `L/K` is finite, every element of `A_L` is integral over `A_K` via base change. -/
theorem isIntegral_baseChangeTo (z : HypRing L g) :
    (HypRing.baseChangeTo f hg).IsIntegralElem z := by
  let : Algebra (HypRing K f) (HypRing L g) := (HypRing.baseChangeTo f hg).toAlgebra
  have halg : algebraMap (HypRing K f) (HypRing L g) = HypRing.baseChangeTo f hg := rfl
  have hcomp : (algebraMap (HypRing K f) (HypRing L g)).comp (algebraMap K (HypRing K f))
      = (algebraMap L (HypRing L g)).comp (algebraMap K L) := by
    rw [halg]; ext a : 1; ext <;> simp [Polynomial.algebraMap_eq]
  have hint (c : L) : IsIntegral (HypRing K f) (algebraMap L (HypRing L g) c) := by
    obtain ⟨P, hPmon, hPev⟩ := Algebra.IsIntegral.isIntegral (R := K) c
    refine ⟨P.map (algebraMap K (HypRing K f)), hPmon.map _, ?_⟩
    rw [eval₂_map, hcomp, ← Polynomial.hom_eval₂ P (algebraMap K L) (algebraMap L (HypRing L g)) c,
      hPev, map_zero]
  have hXint : IsIntegral (HypRing K f) (algebraMap L[X] (HypRing L g) X) := by
    rw [← HypRing.baseChangeTo_algebraMap_X f hg, ← halg]; exact isIntegral_algebraMap
  have hyint : IsIntegral (HypRing K f) (HypRing.y g) := by
    rw [← HypRing.baseChangeTo_y f hg, ← halg]; exact isIntegral_algebraMap
  have hAM (p : L[X]) : IsIntegral (HypRing K f) (algebraMap L[X] (HypRing L g) p) :=
    isIntegral_algebraMap_polynomial
      (fun c ↦ HypRing.algebraMap_eq_C (f := g) c ▸ hint c) hXint p
  rw [HypRing.eq_algebraMap_re_add_im g z]
  exact (hAM z.re).add ((hAM z.im).mul hyint)

variable [NeZero (2 : K)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]
  [NeZero (2 : L)] [Fact (Odd g.natDegree)] [Fact (Squarefree g)]

/-- Every nonzero prime divisor of the extension of `I` divides the extension of a nonzero
prime divisor of `I`. -/
theorem exists_prime_dvd_of_prime_dvd_map {I : Ideal (HypRing K f)}
    {Q : Ideal (HypRing L g)} (hQp : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    (hdvd : Q ∣ I.map (HypRing.baseChangeTo f hg)) :
    ∃ q : Ideal (HypRing K f), q.IsPrime ∧ q ≠ ⊥ ∧ q ∣ I ∧
      Q ∣ q.map (HypRing.baseChangeTo f hg) := by
  set bc := HypRing.baseChangeTo f hg
  let : Algebra (HypRing K f) (HypRing L g) := bc.toAlgebra
  have halg : algebraMap (HypRing K f) (HypRing L g) = bc := rfl
  have : Algebra.IsIntegral (HypRing K f) (HypRing L g) :=
    ⟨fun z ↦ isIntegral_baseChangeTo hg z⟩
  have := hQp
  refine ⟨Q.comap bc, Ideal.comap_isPrime bc Q, ?_, ?_, ?_⟩
  · have := Ideal.IsIntegral.under_ne_bot (HypRing K f) hQ0
    rwa [Ideal.under_def, halg] at this
  · exact Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mp (Ideal.dvd_iff_le.mp hdvd))
  · exact Ideal.dvd_iff_le.mpr Ideal.map_comap_le

end Contraction

end ChabautyColeman

end
