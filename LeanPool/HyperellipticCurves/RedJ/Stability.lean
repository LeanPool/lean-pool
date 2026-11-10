/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.RedJ.Tower

/-!
# Base-change stability of the reduction over the tower

For the tower of finite extensions `L : IntermediateField K (AlgebraicClosure K)` over which the
reduction map on the Jacobian is assembled (`LeanPool.HyperellipticCurves.RedJ.Tower`), we prove
that the
reduction `ChabautyColeman.redIdealBar` of a **split-supported** ideal (all of whose prime divisors
are maximal ideals of rational points, `ChabautyColeman.SplitSupported`) is *unchanged* under a
further base change `L → L'`.

The key input is that base change does not create new prime divisors when everything is already
rational: a split-supported ideal factors into rational point ideals, each of which stays a
maximal (rational) point ideal after base change (`ChabautyColeman.pointIdeal_baseChangeTo`), so
the factorisations of the two sides match term by term. Combined with the compatibility of the
reduction `ChabautyColeman.redres` with `O`-embeddings (`ChabautyColeman.redres_map`), this
gives the main result `ChabautyColeman.redIdealBar_map_of_splitSupported`, the well-definedness
core of `thm:redJ-hom`.
-/

@[expose] public section

open Polynomial IsLocalRing IsDedekindDomain

namespace ChabautyColeman

/-! ### Composition of base changes of the polynomial index -/

section Composition

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K] (f : O[X])
  (L L' : IntermediateField K (AlgebraicClosure K)) [Algebra L L'] [IsScalarTower K L L']

/-- Base-changing `f` from `K` to `L` and then to `L'` agrees with base-changing directly to
`L'`. -/
theorem map_map_algebraMap_eq :
    ((f.map (algebraMap O K)).map (algebraMap K L)).map (algebraMap L L')
      = (f.map (algebraMap O K)).map (algebraMap K L') := by
  rw [map_map, ← IsScalarTower.algebraMap_eq]

end Composition

section Stability

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type u} [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  [IsAlgClosed (ResidueField O)]
  (f : O[X])

/-! ### Reduction over the tower of powers and finite products -/

section Prod

variable (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M]
  [Fact (Odd (f.map (algebraMap O K)).natDegree)] [Fact (Squarefree (f.map (algebraMap O K)))]

/-- The reduction of the unit ideal is the unit ideal. -/
@[simp]
theorem redIdealBar_top :
    redIdealBar f M (⊤ : Ideal (HypRing M ((f.map (algebraMap O K)).map (algebraMap K M))))
      = ⊤ := by
  rw [redIdealBar, Ideal.map_top, redIdeal_top, Ideal.map_top]

/-- The reduction of a power of a nonzero ideal is the corresponding power of the reduction. -/
theorem redIdealBar_pow
    {J : Ideal (HypRing M ((f.map (algebraMap O K)).map (algebraMap K M)))} (hJ : J ≠ 0)
    (n : ℕ) : redIdealBar f M (J ^ n) = redIdealBar f M J ^ n := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, redIdealBar_top]
  | succ n ih => rw [pow_succ, pow_succ, redIdealBar_mul f M (pow_ne_zero n hJ) hJ, ih]

/-- The reduction of a finite product of nonzero ideals is the product of the reductions. -/
theorem redIdealBar_prod {ι : Type*} (s : Finset ι)
    (J : ι → Ideal (HypRing M ((f.map (algebraMap O K)).map (algebraMap K M))))
    (hJ : ∀ i ∈ s, J i ≠ 0) :
    redIdealBar f M (∏ i ∈ s, J i) = ∏ i ∈ s, redIdealBar f M (J i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top, redIdealBar_top]
  | insert a s ha ih =>
      have hne : ∏ i ∈ s, J i ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi ↦ hJ i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        redIdealBar_mul f M (hJ a (Finset.mem_insert_self a s)) hne,
        ih fun i hi ↦ hJ i (Finset.mem_insert_of_mem hi)]

/-- **The reduction of a product of powers of point ideals**: the points whose `x`-coordinate
is not integral reduce to `∞_bar` and drop out of the product; the remaining ones reduce point by
point. -/
theorem redIdealBar_prod_pointIdeal {ι : Type*} (s : Finset ι) {x y : ι → M}
    [DecidablePred fun i ↦ IsIntegral O (x i)] (k : ι → ℕ)
    (hcv : ∀ i ∈ s, y i ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K M)).eval (x i)) :
    redIdealBar f M (∏ i ∈ s, pointIdeal ((f.map (algebraMap O K)).map (algebraMap K M))
        (x i) (y i) ^ k i)
      = ∏ i ∈ s.filter fun i ↦ IsIntegral O (x i),
          pointIdeal (f.map (residue O)) (redres O M (x i)) (redres O M (y i)) ^ k i := by
  rw [redIdealBar_prod f M _ _ fun i _ ↦ pow_ne_zero _ (pointIdeal_ne_zero _ _ _),
    ← Finset.prod_filter_mul_prod_filter_not s fun i ↦ IsIntegral O (x i)]
  have htop i (hi : i ∈ s.filter fun i ↦ ¬IsIntegral O (x i)) :
      redIdealBar f M (pointIdeal ((f.map (algebraMap O K)).map (algebraMap K M))
        (x i) (y i) ^ k i) = ⊤ := by
    rw [redIdealBar_pow f M (pointIdeal_ne_zero _ _ _),
      redIdealBar_pointIdeal_of_not_isIntegral f M (hcv i (Finset.mem_filter.mp hi).1)
        (Finset.mem_filter.mp hi).2, Ideal.top_pow]
  rw [Finset.prod_congr rfl htop, Finset.prod_const, Ideal.top_pow, Ideal.mul_top]
  exact Finset.prod_congr rfl fun i hi ↦ by
    rw [redIdealBar_pow f M (pointIdeal_ne_zero _ _ _),
      redIdealBar_pointIdeal f M (hcv i (Finset.mem_filter.mp hi).1)
        (Finset.mem_filter.mp hi).2]

end Prod

/-! ### Transporting the reduction of a split-supported ideal -/

section MapSplitSupported

variable (L L' : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
  [FiniteDimensional K L']
  [Fact (Odd (f.map (algebraMap O K)).natDegree)] [Fact (Squarefree (f.map (algebraMap O K)))]

/-- **Reduction of a split-supported ideal is transported factor by factor.** Given a ring map `g`
on the curve over the tower and a ring map `h` on the reduced curve that agree on the maximal
ideals of rational points (`hpt`), reduction intertwines them on every split-supported ideal: such
an ideal factors into powers of rational point ideals, and `redIdealBar` turns the factorisation
into a product term by term. The per-point input is base-change stability, with `h` the identity,
or Frobenius equivariance (`upstream HyperellipticCurves.Archive.Equivariance`), with `g` and `h`
the
transports along a compatible automorphism pack. -/
theorem redIdealBar_map_eq_map_of_splitSupported
    (g : HypRing L ((f.map (algebraMap O K)).map (algebraMap K L)) →+*
      HypRing L' ((f.map (algebraMap O K)).map (algebraMap K L')))
    (h : HypRing (ResidueField O) (f.map (residue O)) →+*
      HypRing (ResidueField O) (f.map (residue O)))
    (hg0 : ∀ J : Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L))),
      J ≠ 0 → J.map g ≠ 0)
    (hpt : ∀ x y : L, y ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K L)).eval x →
      redIdealBar f L'
          ((pointIdeal ((f.map (algebraMap O K)).map (algebraMap K L)) x y).map g)
        = (redIdealBar f L
            (pointIdeal ((f.map (algebraMap O K)).map (algebraMap K L)) x y)).map h)
    {I : Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L)))} (hI : I ≠ 0)
    (hs : SplitSupported I) :
    redIdealBar f L' (I.map g) = (redIdealBar f L I).map h := by
  obtain ⟨s, hIeq, hne, hle⟩ := exists_finset_maxPowDividing hI
  have hmap : I.map g = ∏ v ∈ s, (v.maxPowDividing I).map g := by
    nth_rw 1 [← hIeq]
    exact map_prod (Ideal.mapHom g) _ _
  have hLHS : redIdealBar f L' (I.map g)
      = ∏ v ∈ s, redIdealBar f L' ((v.maxPowDividing I).map g) := by
    rw [hmap]; exact redIdealBar_prod f L' _ _ fun v hv ↦ hg0 _ (hne v hv)
  have hRHS : (redIdealBar f L I).map h
      = ∏ v ∈ s, (redIdealBar f L (v.maxPowDividing I)).map h := by
    conv_lhs => rw [show redIdealBar f L I
        = ∏ v ∈ s, redIdealBar f L (v.maxPowDividing I) by
      nth_rw 1 [← hIeq]
      exact redIdealBar_prod f L _ _ hne]
    exact map_prod (Ideal.mapHom h) _ _
  rw [hLHS, hRHS]
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  obtain ⟨x, y, hxy, hqeq⟩ := hs v.asIdeal v.isPrime v.ne_bot (hle v hv)
  have hp0 : pointIdeal ((f.map (algebraMap O K)).map (algebraMap K L)) x y ≠ 0 :=
    pointIdeal_ne_zero _ x y
  rw [HeightOneSpectrum.maxPowDividing, hqeq, Ideal.map_pow, redIdealBar_pow f L' (hg0 _ hp0),
    redIdealBar_pow f L hp0, Ideal.map_pow, hpt x y hxy]

end MapSplitSupported

/-! ### Split-supportedness is preserved by base change -/

section SplitSupportedMap

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
  {g : F[X]} {g' : F'[X]} (hg : g.map (algebraMap F F') = g')
  [NeZero (2 : F)] [Fact (Odd g.natDegree)] [Fact (Squarefree g)]
  [NeZero (2 : F')] [Fact (Odd g'.natDegree)] [Fact (Squarefree g')]

/-- **Split-supportedness is stable under base change.** If every nonzero prime divisor of `I`
is the maximal ideal of a rational point, the same holds for its base change: a nonzero prime
divisor of `I.map` divides the base change of a rational prime divisor of `I`, hence coincides
with the (maximal, rational) base-changed point ideal. -/
theorem SplitSupported.map_baseChangeTo {I : Ideal (HypRing F g)}
    (hs : SplitSupported I) : SplitSupported (I.map (HypRing.baseChangeTo g hg)) := by
  intro Q hQp hQ0 hle
  obtain ⟨q, hqp, hq0, hqI, hQq⟩ :=
    exists_prime_dvd_of_prime_dvd_map hg hQp hQ0 (Ideal.dvd_iff_le.mpr hle)
  obtain ⟨x, y, hxy, hqeq⟩ := hs q hqp hq0 (Ideal.dvd_iff_le.mp hqI)
  have hxy' : (algebraMap F F' y) ^ 2 = g'.eval (algebraMap F F' x) := by
    rw [← hg, eval_map_apply, ← map_pow, hxy]
  have hple : pointIdeal g' (algebraMap F F' x) (algebraMap F F' y) ≤ Q := by
    rw [← pointIdeal_baseChangeTo g hg x y, ← hqeq]
    exact Ideal.dvd_iff_le.mp hQq
  exact ⟨algebraMap F F' x, algebraMap F F' y, hxy',
    ((pointIdeal_isMaximal hxy').eq_of_le hQp.ne_top hple).symm⟩

end SplitSupportedMap

/-! ### Base-change stability of the reduction over the tower -/

section Tower

variable (L L' : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
  [FiniteDimensional K L'] [Algebra L L'] [IsScalarTower K L L']
  [Fact (Odd (f.map (algebraMap O K)).natDegree)] [Fact (Squarefree (f.map (algebraMap O K)))]

/-- **Per-prime base-change stability.** The reduction of the maximal ideal of a rational point
of the curve over `L` is unchanged when the point ideal is base-changed to `L'`: the point ideal
maps to that of the base-changed point, whose coordinate reductions `redres` agree with the
original ones (`redres_map`), and integrality of the `x`-coordinate over `O` is preserved. -/
theorem redIdealBar_map_baseChangeTo_pointIdeal
    {x y : L} (hxy : y ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K L)).eval x) :
    redIdealBar f L'
        ((pointIdeal ((f.map (algebraMap O K)).map (algebraMap K L)) x y).map
          (HypRing.baseChangeTo _ (map_map_algebraMap_eq f L L')))
      = redIdealBar f L (pointIdeal ((f.map (algebraMap O K)).map (algebraMap K L)) x y) := by
  have hst : IsScalarTower O L L' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply O K L', IsScalarTower.algebraMap_apply O K L,
      IsScalarTower.algebraMap_apply K L L']
  have hxy' : (algebraMap L L' y) ^ 2
      = ((f.map (algebraMap O K)).map (algebraMap K L')).eval (algebraMap L L' x) := by
    rw [← map_map_algebraMap_eq f L L', eval_map_apply, ← map_pow, hxy]
  rw [pointIdeal_baseChangeTo _ (map_map_algebraMap_eq f L L') x y]
  by_cases hx : IsIntegral O x
  · have hx' : IsIntegral O (algebraMap L L' x) :=
      hx.map (IsScalarTower.toAlgHom O L L')
    rw [redIdealBar_pointIdeal f L' hxy' hx', redIdealBar_pointIdeal f L hxy hx,
      show redres O L' (algebraMap L L' x) = redres O L x from
        redres_map O L L' (IsScalarTower.toAlgHom O L L') x,
      show redres O L' (algebraMap L L' y) = redres O L y from
        redres_map O L L' (IsScalarTower.toAlgHom O L L') y]
  · have hx' : ¬ IsIntegral O (algebraMap L L' x) := fun hc ↦
      hx ((isIntegral_algHom_iff (IsScalarTower.toAlgHom O L L')
        (algebraMap L L').injective).mp hc)
    rw [redIdealBar_pointIdeal_of_not_isIntegral f L' hxy' hx',
      redIdealBar_pointIdeal_of_not_isIntegral f L hxy hx]

/-- **Base-change stability**: the reduction of a split-supported ideal over the tower is
unchanged under further base change. This is the well-definedness core of `thm:redJ-hom`.

The ideal factors into rational point ideals; base change maps each factor to a maximal rational
point ideal (no new primes appear, `SplitSupported`), so the two factorisations match term by
term via `redIdealBar_map_baseChangeTo_pointIdeal`. -/
theorem redIdealBar_map_of_splitSupported
    {I : Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L)))} (hI : I ≠ 0)
    (hs : SplitSupported I) :
    redIdealBar f L' (I.map (HypRing.baseChangeTo _ (map_map_algebraMap_eq f L L')))
      = redIdealBar f L I := by
  rw [← Ideal.map_id (redIdealBar f L I)]
  refine redIdealBar_map_eq_map_of_splitSupported f L L' _ (RingHom.id _)
    (fun _ hJ ↦ map_baseChangeTo_ne_zero _ _ hJ) (fun x y hxy ↦ ?_) hI hs
  rw [Ideal.map_id]
  exact redIdealBar_map_baseChangeTo_pointIdeal f L L' hxy

end Tower

end Stability

end ChabautyColeman

end
