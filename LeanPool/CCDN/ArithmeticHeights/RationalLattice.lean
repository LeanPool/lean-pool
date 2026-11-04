/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.CauchyBinet
public import LeanPool.CCDN.ArithmeticHeights.GramCovolume
public import LeanPool.CCDN.ArithmeticHeights.Subspace
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.RingTheory.Localization.Integer

/-!
# The lattice of integral points of a rational subspace, and its covolume

For a subspace `V ⊆ ℚ^ι` the integral points `V ∩ ℤ^ι` form a lattice of rank `dim V` in the real
span of `V`, and its covolume is the Arakelov height of `V`:

```text
covolume (V ∩ ℤ^ι)  =  H_Ar V.
```

This is the `ℚ` case of the covolume identity of Layer 4.3 — W. M. Schmidt's `H'(S) = H(S)` — which
over a number field `K` reads `covol (V ∩ 𝓞_K^ι) = 2^{-r₂ k} |discr K|^{k/2} H_Ar(V)^d`. Over `ℚ`
the degree `d`, the discriminant and the number `r₂` of complex places are all `1`, `1` and `0`, so
the three constants vanish and the identity is the bare statement above. It is what converts the
lattice statement of Minkowski's second theorem (Layer 4.2) into a height statement, and it is the
only ingredient Siegel's lemma over `ℚ` takes from this milestone.

## Main definitions

* `Rat.piIntCast`, `Rat.piEuclidean`: the coordinatewise casts `(ι → ℤ) → (ι → ℚ)` and
  `(ι → ℚ) → EuclideanSpace ℝ ι`. The second is the `ℚ` case of `NumberField.mixedEmbedding`.
* `Submodule.intPoints`: the integral points `V ∩ ℤ^ι` of a rational subspace, as a `ℤ`-submodule
  of `ι → ℤ`.
* `Submodule.realSpan`: the real span of a rational subspace, inside `EuclideanSpace ℝ ι`.
* `Submodule.intLattice`: the integral points, as a `ℤ`-lattice inside `Submodule.realSpan`. This
  is the object whose covolume the milestone computes.

## Main results

* `Submodule.covolume_intLattice`: the covolume identity, `covolume (V ∩ ℤ^ι) = H_Ar V`.
* `Submodule.covolume_intLattice_span_singleton`: its rank-one case — the covolume of the lattice
  cut out by a line is the Arakelov height of any rational point spanning it, hence the euclidean
  norm of the primitive integer point on it.
* `Submodule.exists_basis_intPoints`: the integral points are free of rank `dim V`, with a basis
  that spans `V` over `ℚ` and generates *all* of `V ∩ ℤ^ι` — the saturation that makes the height
  come out right.
* `Submodule.gcd_plucker_eq_one`: **the Plücker point of such a basis is a primitive integer
  vector**: the maximal minors of a saturated integral basis are coprime.
* `NumberField.arakelovMulHeight_intCast_of_gcd_eq_one`: over `ℚ`, the Arakelov height of a tuple
  of coprime integers is its euclidean norm. This is the Arakelov analogue of Mathlib's
  `Rat.mulHeight_eq_max_abs_of_gcd_eq_one`, which Mathlib states for the sup norm only.
* `Submodule.finrank_realSpan`, `Submodule.mem_intLattice`, and the `DiscreteTopology` and
  `IsZLattice` instances that make the covolume meaningful.

## Implementation notes

⚠ **Both sides of the identity are computed against the same sum of squares of maximal minors, and
that is the whole proof.** With `y` a saturated integral basis and `p` its tuple of Plücker
coordinates, `ZLattice.covolume_sq_eq_det_gram` and the Cauchy–Binet identity of Layer 3.4 give
`covolume² = det (Y Yᵀ) = ∑ₛ p ₛ²`, while the height is `∑ₛ p ₛ²` under a square root because the
finite places contribute `1` — which is exactly the primitivity of `p`. Neither computation knows
about the other; the identity is the statement that the archimedean factor of the height is a Gram
determinant and its finite factor is a saturation condition.

⚠ **Saturation is not a convenience, it is the content.** For an arbitrary `ℤ`-basis of a
finite-index sublattice of `V ∩ ℤ^ι` the covolume is larger by the index, while the height does not
change: the Plücker coordinates are multiplied by the index and the extra factor is cancelled by
the finite places. `Submodule.gcd_plucker_eq_one` is where saturation is spent, and it is spent
exactly once.

⚠ **The primitivity proof needs no adapted basis, no Smith normal form and no splitting of the
quotient.** If a prime `q` divided every maximal minor of `y`, then the reductions of the `y i`
would be linearly dependent over `ZMod q` — this is `exteriorPower.plucker_eq_zero_iff` of Layer
3.1, read over a finite field — so some integral combination `∑ cᵢ yᵢ` with a coefficient prime to
`q` would be divisible by `q`; its quotient by `q` is an integral point of `V`, hence a
`ℤ`-combination of the `y i` by saturation, and independence then forces `q ∣ cᵢ` for every `i`.
Cassels' Lemma 2 is not on this path either, just as it was not on the path of Layer 4.2.

⚠ **The lattice lives in a subspace, and that is why the ambient space is `EuclideanSpace`.** A
sublattice of `ℤ^ι` of rank `k < #ι` has no covolume in `ℝ^ι`; the covolume it has is the one
measured inside its own real span, and a subspace of a real vector space carries a canonical
measure only when the space carries an inner product. `Submodule.realSpan` is therefore a submodule
of `EuclideanSpace ℝ ι` rather than of `ι → ℝ`, and `ZLattice.covolume` is taken against the
`MeasureSpace` instance that `Mathlib.MeasureTheory.Measure.Haar.OfBasis` puts on any
finite-dimensional real inner product space.

⚠ **Only the `ℚ` case is here.** The number-field case of Layer 4.3 is Schmidt 1967, §3, Theorem 1,
whose two halves — a Lagrange expansion in blocks of `d` rows for the archimedean factor, and a
local counting lemma for `[σ(Λ) : Λ₀] = N(𝔞)` at the finite places — are not reproduced here. What
the `ℚ` case already settles is the shape of the statement and its normalization: the Arakelov
height, not the sup-norm height, is what a covolume equals.

## References

W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §3, Theorem 1: `H'(S) = H(S)`, of which the statement here is
the case `K = ℚ`. His Lemma 4 is the archimedean half — over `ℚ` it is the Cauchy–Binet identity
alone — and his Lemmas 5 and 6 the finite half, which over `ℚ` is the primitivity of the Plücker
point.

I. Aliev and M. Henk, "Minkowski's successive minima in convex and discrete geometry",
*Communications in Mathematics* **31**(2) (2023), 35–59, §6
(arXiv:2304.00120; doi:10.46298/cm.11155). The rational covolume identity is stated
immediately before Theorem 6.3 and used in the geometry-of-numbers proof of Siegel's lemma.

This is Layer 4.3 of the `ArithmeticHeights` roadmap, over `ℚ`.
-/

public section

open Module Submodule

/-!
### The two coordinatewise casts
-/

/-- Coordinatewise `ℤ → ℚ` on tuples, as a `ℤ`-linear map. -/
@[expose] def Rat.piIntCast (ι : Type*) : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun z i := (z i : ℚ)
  map_add' a b := by funext i; simp
  map_smul' c a := by funext i; simp

@[simp] theorem Rat.piIntCast_apply {ι : Type*} (z : ι → ℤ) (i : ι) :
    Rat.piIntCast ι z i = (z i : ℚ) := rfl

theorem Rat.piIntCast_injective {ι : Type*} : Function.Injective (Rat.piIntCast ι) :=
  fun _ _ h ↦ funext fun i ↦ by
    have hi := congrFun h i
    rw [Rat.piIntCast_apply, Rat.piIntCast_apply] at hi
    exact_mod_cast hi

/-- Coordinatewise `ℚ → ℝ` on tuples, landing in `EuclideanSpace ℝ ι`, as a `ℚ`-linear map. This
is the `ℚ` case of `NumberField.mixedEmbedding`: there are no complex places and the one real
place is the inclusion. -/
@[expose] def Rat.piEuclidean (ι : Type*) : (ι → ℚ) →ₗ[ℚ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 fun i ↦ ((x i : ℝ))
  map_add' a b := by ext i; push_cast; simp
  map_smul' c a := by ext i; push_cast; simp [Rat.smul_def]

@[simp] theorem Rat.piEuclidean_apply {ι : Type*} (x : ι → ℚ) (i : ι) :
    (Rat.piEuclidean ι x).ofLp i = (x i : ℝ) := rfl

/-!
### The integral points of a rational subspace
-/

section IntPoints

variable {ι : Type*}

/-- The **integral points** `V ∩ ℤ^ι` of a rational subspace, as a `ℤ`-submodule of `ι → ℤ`. -/
@[expose] def Submodule.intPoints (V : Submodule ℚ (ι → ℚ)) : Submodule ℤ (ι → ℤ) :=
  Submodule.comap (Rat.piIntCast ι) (V.restrictScalars ℤ)

@[simp] theorem Submodule.mem_intPoints {V : Submodule ℚ (ι → ℚ)} {z : ι → ℤ} :
    z ∈ V.intPoints ↔ Rat.piIntCast ι z ∈ V := Iff.rfl

/-- A `ℤ`-basis of the integral points is linearly independent over `ℚ`. -/
private theorem linearIndependent_of_basis_intPoints (V : Submodule ℚ (ι → ℚ)) {κ : Type*}
    (b : Basis κ ℤ V.intPoints) :
    LinearIndependent ℚ fun i ↦ Rat.piIntCast ι (b i : ι → ℤ) := by
  rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
  exact b.linearIndependent.map' ((Rat.piIntCast ι).comp (V.intPoints.subtype))
    (LinearMap.ker_eq_bot.2 (Rat.piIntCast_injective.comp V.intPoints.injective_subtype))

/-- A `ℤ`-basis of the integral points generates all of them: saturation. -/
private theorem span_int_of_basis_intPoints (V : Submodule ℚ (ι → ℚ)) {κ : Type*}
    (b : Basis κ ℤ V.intPoints) :
    Submodule.span ℤ (Set.range fun i ↦ (b i : ι → ℤ)) = V.intPoints := by
  rw [show (fun i ↦ ((b i : ι → ℤ))) = (V.intPoints.subtype ∘ b) from rfl, Set.range_comp,
    ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

variable [Finite ι]

instance (V : Submodule ℚ (ι → ℚ)) : Module.Finite ℤ V.intPoints :=
  Module.Finite.of_injective V.intPoints.subtype V.intPoints.injective_subtype

instance (V : Submodule ℚ (ι → ℚ)) : Module.Free ℤ V.intPoints :=
  Module.free_of_finite_type_torsion_free'

/-- Clearing denominators: every rational tuple has a nonzero integral multiple. -/
private theorem exists_intCast_smul (v : ι → ℚ) :
    ∃ (N : ℤ) (z : ι → ℤ), N ≠ 0 ∧ (N : ℚ) • v = Rat.piIntCast ι z := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
    (Finset.univ : Finset ι) v
  choose z hz using fun i ↦ hb i (Finset.mem_univ i)
  refine ⟨(b : ℤ), z, nonZeroDivisors.coe_ne_zero b, funext fun i ↦ ?_⟩
  have h := hz i
  simp only [Algebra.smul_def, algebraMap_int_eq, eq_intCast] at h
  simpa using h.symm

/-- A `ℤ`-basis of the integral points spans `V` over `ℚ`. -/
private theorem span_of_basis_intPoints (V : Submodule ℚ (ι → ℚ)) {κ : Type*}
    (b : Basis κ ℤ V.intPoints) :
    Submodule.span ℚ (Set.range fun i ↦ Rat.piIntCast ι (b i : ι → ℤ)) = V := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun v hv ↦ ?_
  · rintro _ ⟨i, rfl⟩
    exact (b i).2
  · obtain ⟨N, z, hN, hz⟩ := exists_intCast_smul v
    have hzΛ : z ∈ V.intPoints := by
      rw [Submodule.mem_intPoints, ← hz]
      exact V.smul_mem _ hv
    have h1 : (⟨z, hzΛ⟩ : V.intPoints) ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; exact Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := (Rat.piIntCast ι).comp (V.intPoints.subtype)) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    have h3 : Rat.piIntCast ι z ∈
        Submodule.span ℚ (Set.range fun i ↦ Rat.piIntCast ι (b i : ι → ℤ)) :=
      Submodule.span_le_restrictScalars ℤ ℚ _ h2
    have hNQ : (N : ℚ) ≠ 0 := Int.cast_ne_zero.2 hN
    rw [show v = (N : ℚ)⁻¹ • Rat.piIntCast ι z by
      rw [← hz, smul_smul, inv_mul_cancel₀ hNQ, one_smul]]
    exact Submodule.smul_mem _ _ h3

/-- **A saturated integral basis exists.** The integral points of a rational subspace of dimension
`k` are a free `ℤ`-module of rank `k`, and a basis of them spans `V` over `ℚ` while generating
*every* integral point of `V`. Both halves are needed: the first makes the basis a basis of the
real span, the second is what makes its Plücker point primitive. -/
theorem Submodule.exists_basis_intPoints (V : Submodule ℚ (ι → ℚ)) {k : ℕ}
    (hV : finrank ℚ V = k) :
    ∃ y : Fin k → (ι → ℤ),
      LinearIndependent ℚ (fun i ↦ Rat.piIntCast ι (y i)) ∧
      Submodule.span ℚ (Set.range fun i ↦ Rat.piIntCast ι (y i)) = V ∧
      Submodule.span ℤ (Set.range y) = V.intPoints := by
  classical
  let b₀ := Module.Free.chooseBasis ℤ V.intPoints
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ V.intPoints) = k := by
    have h := finrank_span_eq_card (linearIndependent_of_basis_intPoints V b₀)
    rw [span_of_basis_intPoints V b₀, hV] at h
    exact h.symm
  let b := b₀.reindex (Fintype.equivFinOfCardEq hcard)
  exact ⟨fun i ↦ (b i : ι → ℤ), linearIndependent_of_basis_intPoints V b,
    span_of_basis_intPoints V b, span_int_of_basis_intPoints V b⟩

end IntPoints

/-!
### Primitivity of the Plücker point
-/

section Primitive

open exteriorPower

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (V : Submodule ℚ (ι → ℚ))

/-- **The maximal minors of a saturated integral basis are coprime.** Equivalently: the Plücker
point of a rational subspace has a primitive integer representative, namely the one a basis of
`V ∩ ℤ^ι` produces. This is the finite half of the covolume identity — Schmidt's Lemmas 5 and 6
over `ℚ` — and it is the only place the saturation hypothesis is used. -/
theorem Submodule.gcd_plucker_eq_one {k : ℕ} {y : Fin k → (ι → ℤ)}
    (hy : LinearIndependent ℚ (fun i ↦ Rat.piIntCast ι (y i)))
    (hspan : Submodule.span ℚ (Set.range fun i ↦ Rat.piIntCast ι (y i)) = V)
    (hsat : Submodule.span ℤ (Set.range y) = V.intPoints) :
    (Finset.univ : Finset (Set.powersetCard ι k)).gcd (plucker k y) = 1 := by
  classical
  have hyZ : LinearIndependent ℤ y :=
    LinearIndependent.of_comp (Rat.piIntCast ι)
      (hy.restrict_scalars (by simpa using Int.cast_injective (α := ℚ)))
  have key : ∀ q : ℤ, Prime q → ¬ (∀ s, q ∣ plucker k y s) := by
    intro q hq hdvd
    set P := q.natAbs with hP
    have hPp : P.Prime := Int.prime_iff_natAbs_prime.1 hq
    have : Fact P.Prime := ⟨hPp⟩
    have hPdvd : ∀ s, ((P : ℤ)) ∣ plucker k y s := fun s ↦
      (Int.natAbs_dvd.2 dvd_rfl).trans (hdvd s)
    have hzero : plucker k (fun i ↦ (Int.castRingHom (ZMod P)) ∘ y i) = 0 := by
      funext s
      rw [plucker_map]
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).2 (hPdvd s)
    obtain ⟨c, hcsum, i₀, hi₀⟩ :=
      Fintype.not_linearIndependent_iff.1 ((plucker_eq_zero_iff (K := ZMod P) k _).1 hzero)
    choose c' hc' using fun i ↦ ZMod.intCast_surjective (n := P) (c i)
    set w : ι → ℤ := fun l ↦ ∑ i, c' i * y i l with hw
    have hwdvd : ∀ l, ((P : ℤ)) ∣ w l := by
      intro l
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hl := congrFun hcsum l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Function.comp_apply, eq_intCast] at hl
      have hcast : ((w l : ℤ) : ZMod P) = ∑ i, c i * ((y i l : ℤ) : ZMod P) := by
        rw [hw]
        push_cast
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hc' i]
      rw [hcast, hl]
    choose z hz using hwdvd
    have hwz : w = (P : ℤ) • z := funext fun l ↦ by simp [hz l]
    have hwV : Rat.piIntCast ι w ∈ V := by
      rw [← hspan, show Rat.piIntCast ι w = ∑ i, (c' i : ℚ) • Rat.piIntCast ι (y i) from
        funext fun l ↦ by simp [hw, Finset.sum_apply]]
      exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hPQ : ((P : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hPp.ne_zero
    have hzV : Rat.piIntCast ι z ∈ V := by
      have h1 : Rat.piIntCast ι w = (P : ℚ) • Rat.piIntCast ι z := by
        rw [hwz, map_zsmul]; funext l; simp
      have h2 := V.smul_mem ((P : ℚ)⁻¹) hwV
      rwa [h1, smul_smul, inv_mul_cancel₀ hPQ, one_smul] at h2
    obtain ⟨d, hd⟩ := (mem_span_range_iff_exists_fun ℤ).1 (by rw [hsat]; exact hzV :
      z ∈ Submodule.span ℤ (Set.range y))
    have hcoef : ∀ i, c' i - (P : ℤ) * d i = 0 := by
      refine Fintype.linearIndependent_iff.1 hyZ _ ?_
      have h1 : ∑ i, c' i • y i = w := funext fun l ↦ by simp [hw, Finset.sum_apply]
      have h2 : ∑ i, ((P : ℤ) * d i) • y i = w := by
        rw [hwz, ← hd]
        exact funext fun l ↦ by simp [Finset.mul_sum, Finset.sum_apply, mul_assoc]
      simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]
    refine hi₀ ?_
    rw [← hc' i₀, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨d i₀, by linarith [hcoef i₀]⟩
  have hgu : IsUnit ((Finset.univ : Finset (Set.powersetCard ι k)).gcd (plucker k y)) := by
    rw [Int.isUnit_iff_natAbs_eq]
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Int.exists_prime_and_dvd hne
    exact key q hq fun s ↦ hqd.trans (Finset.gcd_dvd (Finset.mem_univ s))
  calc (Finset.univ : Finset (Set.powersetCard ι k)).gcd (plucker k y)
      = normalize ((Finset.univ : Finset (Set.powersetCard ι k)).gcd (plucker k y)) :=
        Finset.normalize_gcd.symm
    _ = 1 := normalize_eq_one.2 hgu

end Primitive

/-!
### The real span and the lattice inside it
-/

section RealSpan

variable {ι : Type*}

/-- The **real span** of a rational subspace, inside `EuclideanSpace ℝ ι`. -/
@[expose] def Submodule.realSpan (V : Submodule ℚ (ι → ℚ)) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  Submodule.span ℝ (Rat.piEuclidean ι '' (V : Set (ι → ℚ)))

/-- The **integral points of `V` as a lattice in its real span**: the object whose covolume is the
Arakelov height of `V`. -/
@[expose] noncomputable def Submodule.intLattice (V : Submodule ℚ (ι → ℚ)) :
    Submodule ℤ ↥V.realSpan :=
  Submodule.comap ((V.realSpan.subtype).restrictScalars ℤ)
    (Submodule.map (((Rat.piEuclidean ι).restrictScalars ℤ).comp (Rat.piIntCast ι)) V.intPoints)

theorem Submodule.mem_intLattice {V : Submodule ℚ (ι → ℚ)} {w : ↥V.realSpan} :
    w ∈ V.intLattice ↔ ∃ z : ι → ℤ, Rat.piIntCast ι z ∈ V ∧
      (w : EuclideanSpace ℝ ι) = Rat.piEuclidean ι (Rat.piIntCast ι z) := by
  simp only [Submodule.intLattice, Submodule.mem_comap, Submodule.mem_map,
    LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, Submodule.mem_intPoints]
  exact ⟨fun ⟨z, hz, h⟩ ↦ ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ ↦ ⟨z, hz, h.symm⟩⟩

private theorem realSpan_eq (V : Submodule ℚ (ι → ℚ)) {k : ℕ} {y : Fin k → (ι → ℤ)}
    (hspan : Submodule.span ℚ (Set.range fun i ↦ Rat.piIntCast ι (y i)) = V) :
    V.realSpan =
      Submodule.span ℝ (Set.range fun i ↦ Rat.piEuclidean ι (Rat.piIntCast ι (y i))) := by
  subst hspan
  rw [Submodule.realSpan, ← Submodule.map_coe (Rat.piEuclidean ι), Submodule.map_span,
    ← Set.range_comp, Submodule.span_span_of_tower ℚ ℝ]
  rfl

variable [Finite ι]

private theorem linearIndependent_euclidean {k : ℕ} {y : Fin k → (ι → ℤ)}
    (hy : LinearIndependent ℚ (fun i ↦ Rat.piIntCast ι (y i))) :
    LinearIndependent ℝ fun i ↦ Rat.piEuclidean ι (Rat.piIntCast ι (y i)) := by
  have h := (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)
    (v := fun i ↦ Rat.piIntCast ι (y i))).2 hy
  have h' : LinearIndependent ℝ fun i ↦ (fun l ↦ ((y i l : ℤ) : ℝ)) := by
    convert h using 2 with i
    funext l
    simp
  exact h'.map' (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap
    (LinearMap.ker_eq_bot.2 (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.injective)

/-- The construction behind every statement below: a saturated integral basis of `V ∩ ℤ^ι`, read
as an `ℝ`-basis of the real span whose `ℤ`-span is the lattice. -/
private theorem exists_basis_intLattice (V : Submodule ℚ (ι → ℚ)) :
    ∃ (y : Fin (finrank ℚ V) → (ι → ℤ)) (b : Basis (Fin (finrank ℚ V)) ℝ ↥V.realSpan),
      (∀ i, (b i : EuclideanSpace ℝ ι) = Rat.piEuclidean ι (Rat.piIntCast ι (y i))) ∧
      V.intLattice = Submodule.span ℤ (Set.range b) ∧
      Submodule.span ℚ (Set.range fun i ↦ Rat.piIntCast ι (y i)) = V ∧
      LinearIndependent ℚ (fun i ↦ Rat.piIntCast ι (y i)) ∧
      Submodule.span ℤ (Set.range y) = V.intPoints := by
  classical
  obtain ⟨y, hyli, hyspan, hysat⟩ := V.exists_basis_intPoints rfl
  have hE : LinearIndependent ℝ fun i ↦ Rat.piEuclidean ι (Rat.piIntCast ι (y i)) :=
    linearIndependent_euclidean hyli
  have hW : V.realSpan =
      Submodule.span ℝ (Set.range fun i ↦ Rat.piEuclidean ι (Rat.piIntCast ι (y i))) :=
    realSpan_eq V hyspan
  have hmem : ∀ i, Rat.piEuclidean ι (Rat.piIntCast ι (y i)) ∈ V.realSpan := fun i ↦ by
    rw [hW]; exact Submodule.subset_span ⟨i, rfl⟩
  have hliW : LinearIndependent ℝ fun i ↦ (⟨_, hmem i⟩ : ↥V.realSpan) :=
    LinearIndependent.of_comp V.realSpan.subtype hE
  have hspW : ⊤ ≤ Submodule.span ℝ (Set.range fun i ↦ (⟨_, hmem i⟩ : ↥V.realSpan)) := by
    rw [← Submodule.map_le_map_iff_of_injective V.realSpan.injective_subtype,
      Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact le_of_eq hW
  refine ⟨y, Basis.mk hliW hspW, fun i ↦ by rw [Basis.coe_mk], ?_, hyspan, hyli, hysat⟩
  rw [Basis.coe_mk, Submodule.intLattice, ← hysat, Submodule.map_span, ← Set.range_comp]
  rw [show ((Submodule.span ℤ (Set.range (fun i ↦ (⟨_, hmem i⟩ : ↥V.realSpan))))) =
      Submodule.comap ((V.realSpan.subtype).restrictScalars ℤ)
        (Submodule.map ((V.realSpan.subtype).restrictScalars ℤ)
          (Submodule.span ℤ (Set.range (fun i ↦ (⟨_, hmem i⟩ : ↥V.realSpan))))) from
    (Submodule.comap_map_eq_self (by simp)).symm]
  congr 1
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

instance (V : Submodule ℚ (ι → ℚ)) : DiscreteTopology V.intLattice := by
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨_, b, _, hL, _⟩ := exists_basis_intLattice V
  rw [hL]
  infer_instance

/-- The real span of a rational subspace has the dimension of the subspace. -/
theorem Submodule.finrank_realSpan (V : Submodule ℚ (ι → ℚ)) :
    finrank ℝ ↥V.realSpan = finrank ℚ V := by
  obtain ⟨_, b, _⟩ := exists_basis_intLattice V
  simpa using finrank_eq_card_basis b

end RealSpan

section RealSpanZLattice

variable {ι : Type*} [Fintype ι]

instance (V : Submodule ℚ (ι → ℚ)) : IsZLattice ℝ V.intLattice := by
  obtain ⟨_, b, _, hL, _⟩ := exists_basis_intLattice V
  constructor
  rw [hL]
  exact ZSpan.span_top b

end RealSpanZLattice

/-!
### The Arakelov height of a primitive integer tuple
-/

/-- **Over `ℚ` the Arakelov height of a tuple of coprime integers is its euclidean norm.** The
finite places contribute `1` — this is Mathlib's `Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one`
— and the single infinite place is real, so the archimedean factor is the ℓ² norm with exponent
`1`. Mathlib's `Rat.mulHeight_eq_max_abs_of_gcd_eq_one` is the same statement for the sup norm. -/
theorem NumberField.arakelovMulHeight_intCast_of_gcd_eq_one {κ : Type*} [Fintype κ] {x : κ → ℤ}
    (hx : (Finset.univ : Finset κ).gcd x = 1) :
    NumberField.arakelovMulHeight (((↑) : ℤ → ℚ) ∘ x) = Real.sqrt (∑ i, ((x i : ℝ)) ^ 2) := by
  have hne : Nonempty κ := by
    by_contra h
    simp only [not_nonempty_iff] at h
    rw [Finset.univ_eq_empty, Finset.gcd_empty] at hx
    exact zero_ne_one hx
  have hx₀ : ((↑) : ℤ → ℚ) ∘ x ≠ 0 := by
    contrapose! hx
    rw [Function.comp_eq_zero_iff x Rat.intCast_injective Rat.intCast_zero] at hx
    rw [hx, Finset.gcd_eq_zero_iff.mpr (by simp)]
    exact zero_ne_one
  rw [NumberField.arakelovMulHeight_eq hx₀]
  simp only [Function.comp_apply]
  have hmult : (default : NumberField.InfinitePlace ℚ).mult = 1 := by
    rw [Subsingleton.elim (default : NumberField.InfinitePlace ℚ) Rat.infinitePlace]
    exact NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace
  rw [finprod_eq_one_of_forall_eq_one (Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one · hx),
    mul_one, Fintype.prod_unique, hmult]
  have hterm : ∀ i : κ, (default : NumberField.InfinitePlace ℚ) ((x i : ℚ)) ^ 2
      = ((x i : ℝ)) ^ 2 := fun i ↦ by
    rw [Rat.infinitePlace_apply]
    push_cast
    rw [sq_abs]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Real.sqrt_eq_rpow]
  norm_num

/-!
### The covolume identity
-/

section Covolume

open Matrix exteriorPower

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private theorem plucker_piIntCast (k : ℕ) (y : Fin k → (ι → ℤ)) (s : Set.powersetCard ι k) :
    plucker k (fun i ↦ Rat.piIntCast ι (y i)) s = ((plucker k y s : ℤ) : ℚ) := by
  rw [show (fun i ↦ Rat.piIntCast ι (y i)) = (fun i ↦ ((Int.castRingHom ℚ) ∘ y i)) from rfl]
  exact plucker_map _ k y s

private theorem plucker_intCast_real (k : ℕ) (y : Fin k → (ι → ℤ)) (s : Set.powersetCard ι k) :
    plucker k (fun i ↦ (fun l ↦ ((y i l : ℤ) : ℝ))) s = ((plucker k y s : ℤ) : ℝ) := by
  rw [show (fun i ↦ (fun l ↦ ((y i l : ℤ) : ℝ))) = (fun i ↦ ((Int.castRingHom ℝ) ∘ y i)) from rfl]
  exact plucker_map _ k y s

private theorem covolume_eq_of_basis {k : ℕ} {V : Submodule ℚ (ι → ℚ)}
    {y : Fin k → (ι → ℤ)} {b : Basis (Fin k) ℝ ↥V.realSpan}
    (hb : ∀ i, (b i : EuclideanSpace ℝ ι) = Rat.piEuclidean ι (Rat.piIntCast ι (y i)))
    (hL : V.intLattice = Submodule.span ℤ (Set.range b))
    (hspan : Submodule.span ℚ (Set.range fun i ↦ Rat.piIntCast ι (y i)) = V)
    (hli : LinearIndependent ℚ (fun i ↦ Rat.piIntCast ι (y i)))
    (hgcd : (Finset.univ : Finset (Set.powersetCard ι k)).gcd (plucker k y) = 1) :
    ZLattice.covolume V.intLattice = V.arakelovMulHeight := by
  classical
  have hcov : ZLattice.covolume V.intLattice ^ 2
      = ∑ s : Set.powersetCard ι k, ((plucker k y s : ℤ) : ℝ) ^ 2 := by
    rw [hL, ZLattice.covolume_sq_eq_det_gram _ (b.restrictScalars ℤ)]
    have hgram : (Matrix.of fun i j ↦ inner ℝ
        ((b.restrictScalars ℤ) i : ↥V.realSpan) ((b.restrictScalars ℤ) j : ↥V.realSpan))
        = (Matrix.of fun i l ↦ ((y i l : ℤ) : ℝ)) *
            (Matrix.of fun i l ↦ ((y i l : ℤ) : ℝ))ᵀ := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [Basis.restrictScalars_apply, Submodule.coe_inner, Matrix.of_apply,
        Matrix.transpose_apply]
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [hb i, hb j]
      simp [RCLike.inner_apply, mul_comm]
    rw [hgram, Matrix.det_mul_transpose_self_eq_sum_sq]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [show (Matrix.of fun i l ↦ ((y i l : ℤ) : ℝ)).row
        = (fun i ↦ (fun l ↦ ((y i l : ℤ) : ℝ))) from rfl, plucker_intCast_real]
  have hH : V.arakelovMulHeight
      = Real.sqrt (∑ s : Set.powersetCard ι k, ((plucker k y s : ℤ) : ℝ) ^ 2) := by
    rw [← hspan, Submodule.arakelovMulHeight_span_range hli,
      show plucker k (fun i ↦ Rat.piIntCast ι (y i)) = ((↑) : ℤ → ℚ) ∘ (plucker k y) from
        funext fun s ↦ plucker_piIntCast k y s]
    exact NumberField.arakelovMulHeight_intCast_of_gcd_eq_one hgcd
  rw [hH, ← hcov, Real.sqrt_sq (ZLattice.covolume_pos _ _).le]

/-- **The covolume identity over `ℚ`** (Layer 4.3, the case `K = ℚ`; W. M. Schmidt 1967, §3,
Theorem 1). The lattice of integral points of a rational subspace has covolume the Arakelov height
of the subspace. -/
theorem Submodule.covolume_intLattice (V : Submodule ℚ (ι → ℚ)) :
    ZLattice.covolume V.intLattice = V.arakelovMulHeight := by
  obtain ⟨y, b, hb, hL, hspan, hli, hsat⟩ := exists_basis_intLattice V
  exact covolume_eq_of_basis hb hL hspan hli (V.gcd_plucker_eq_one hli hspan hsat)

/-- **The rank-one case.** The lattice cut out by the line through a nonzero rational point has
covolume the Arakelov height of that point — for a primitive integer point, its euclidean norm. -/
theorem Submodule.covolume_intLattice_span_singleton {x : ι → ℚ} (hx : x ≠ 0) :
    ZLattice.covolume (Submodule.span ℚ {x}).intLattice = NumberField.arakelovMulHeight x := by
  rw [Submodule.covolume_intLattice, Submodule.arakelovMulHeight_span_singleton hx]

end Covolume

end
