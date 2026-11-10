/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OmegaExpansion
public import LeanPool.HyperellipticCurves.Series.AntiderivZeros
public import LeanPool.HyperellipticCurves.Series.FractionTopology

/-!
# The per-disk bound

The analytic core of blueprint `thm:disk-bound`. On one residue disk the annihilating
differential integrates to a single convergent function: by the glue identity
(`ChabautyColeman.lambda_glue`) the difference of its values at two rational points of the
disk is `λ_ω` of the difference of their classes, which vanishes because `ω` annihilates the
Jacobian. So the parameters of the rational points of the disk are zeros of one power series,
and `ChabautyColeman.PSeries.antideriv_zeros_le` bounds their number by `m + 1`.

Three steps are needed to run that argument on the objects the two sides produce.

* `ChabautyColeman.PSeries.encard_le_of_evalT_const`: a *constant* value is as good as a zero
  — subtract it (`ChabautyColeman.PSeries.evalT_sub_C` leaves the higher coefficients, hence
  the hypotheses of the zero count, untouched).
* `ChabautyColeman.PSeries.hasSum_algebraMap_evalT`: the value produced by the glue identity
  is a sum over `K = Frac O` of the antiderivative `G` at a point of `𝔪`, while the zero count
  runs on the *substituted* series `H(u) = G(π·u)` over `O`, `π` a uniformizer. The two
  agree, coefficientwise.
* `ChabautyColeman.PSeries.algebraMap_coeff_eq_coeff_antideriv`: that `H` — which
  `ChabautyColeman.PSeries.exists_substituted_antideriv` constructs from the disk expansion —
  does compute the antiderivative `G` of the expansion over `K`, coefficient by coefficient.

`ChabautyColeman.disk_count_le` combines them: for points of one disk with distinct
parameters in `𝔪` at which the integral takes one and the same value, there are at most
`m + 1`. (The rationality-aware per-chart instances live in
`LeanPool.HyperellipticCurves.Count.DiskRational`
and its Weierstrass/infinity companions.)

Blueprint node: `thm:disk-bound`.
-/

@[expose] public section

open PowerSeries IsLocalRing Filter Topology
open ChabautyColeman.FractionTopology

namespace ChabautyColeman

namespace PSeries

section Count

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  {π : O} {p e m : ℕ} {w H : O⟦X⟧}
  (hram : IsUniformizer π p e)
  (hH : ∀ k : ℕ, ((k : O) + 1) * coeff (k + 1) H = π ^ (k + 1) * coeff k w)

include hram hH in
/-- **A constant value of an antiderivative is attained at most `m + 1` times**: the points
at which the substituted antiderivative `H` takes one and the same value are zeros of
`H` minus that value, which satisfies the same coefficient recursion. -/
theorem encard_le_of_evalT_const (hord : m + e + 1 < p) (hmu : IsUnit (coeff m w))
    {α : Type*} {S : Set α} (z : α → O) (hinj : Set.InjOn z S)
    (hconst : ∀ P ∈ S, ∀ Q ∈ S, evalT (z P) H = evalT (z Q) H) :
    S.encard ≤ m + 1 := by
  have hpe : e + 1 < p := by lia
  rcases S.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩
  · simp
  set H' := H - PowerSeries.C (evalT (z P₀) H) with hH'def
  have hH' (k : ℕ) : ((k : O) + 1) * coeff (k + 1) H' = π ^ (k + 1) * coeff k w := by
    rw [hH'def, map_sub, PowerSeries.coeff_C, ite_eq_right (Nat.succ_ne_zero k), sub_zero, hH]
  have hzero (P : α) (hP : P ∈ S) : evalT (z P) H' = 0 := by
    rw [hH'def, evalT_sub_C (tendsto_coeff_antideriv hram hpe hH), hconst P hP P₀ hP₀, sub_self]
  calc S.encard = (z '' S).encard := hinj.encard_image.symm
    _ ≤ ({u : O | evalT u H' = 0}).encard :=
        Set.encard_mono (by rintro _ ⟨P, hP, rfl⟩; exact hzero P hP)
    _ = ({u : O | evalT u H' = 0}).ncard :=
        (antideriv_zeros_finite hram hH' hord hmu).cast_ncard_eq.symm
    _ ≤ m + 1 := mod_cast antideriv_zeros_le hram hH' hord hmu

end Count

section Bridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {π : O} {p e : ℕ} {H : O⟦X⟧}

/-- **The substituted series is the antiderivative, rescaled**: the coefficients of a series
`H` satisfying the recursion of `ChabautyColeman.PSeries.exists_substituted_antideriv` are
those of the antiderivative of `W` over the fraction field, scaled by `πᵏ` for the
uniformizer `π` of the recursion. This is the hypothesis `hGH` below, for `G` the
antiderivative of `W`. -/
theorem algebraMap_coeff_eq_coeff_antideriv [CharZero O] {W : O⟦X⟧}
    (hH : ∀ k : ℕ, ((k : O) + 1) * coeff (k + 1) H = π ^ (k + 1) * coeff k W)
    (hH0 : constantCoeff H = 0) (k : ℕ) :
    algebraMap O (FractionRing O) (coeff k H)
      = coeff k (antideriv (W.map (algebraMap O (FractionRing O))))
        * algebraMap O (FractionRing O) (π ^ k) := by
  rw [← coeff_zero_eq_constantCoeff_apply] at hH0
  rcases k with _ | k
  · simp [hH0, coeff_antideriv]
  · -- nonzeroness for the `field_simp` below
    have hne : ((k : FractionRing O) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    have hk := congrArg (algebraMap O (FractionRing O)) (hH k)
    rw [coeff_succ_antideriv, PowerSeries.coeff_map]
    push_cast at hk ⊢
    field_simp
    linear_combination hk

-- the two facts every consumer of an integral disk expansion needs at once
private theorem exists_coeff_eq_of_antideriv [CharZero O] (hram : IsUniformizer π p e)
    (hpe : e + 1 < p) (W : O⟦X⟧) {G : PowerSeries (FractionRing O)}
    (hGW : G = antideriv (W.map (algebraMap O (FractionRing O)))) :
    ∃ H : O⟦X⟧, (∀ k : ℕ, ((k : O) + 1) * coeff (k + 1) H = π ^ (k + 1) * coeff k W)
      ∧ ∀ k, algebraMap O (FractionRing O) (coeff k H)
          = coeff k G * algebraMap O (FractionRing O) (π ^ k) := by
  obtain ⟨H, hH0, hH⟩ := exists_substituted_antideriv hram hpe W
  exact ⟨H, hH, fun k ↦ hGW ▸ algebraMap_coeff_eq_coeff_antideriv hH hH0 k⟩

variable [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [IsTopologicalRing O]

/-- **The value of an antiderivative on a disk is a value of the substituted series**: the
sum over `K = Frac O` of `G` at the point `π·u` of the maximal ideal is the value at `u` of
the integral series `H`, whose coefficients are those of `G` scaled by `πᵏ`. -/
theorem hasSum_algebraMap_evalT (hdec : Tendsto (fun k ↦ coeff k H) atTop (𝓝 0))
    {G : PowerSeries (FractionRing O)}
    (hGH : ∀ k, algebraMap O (FractionRing O) (coeff k H)
      = coeff k G * algebraMap O (FractionRing O) (π ^ k))
    (u : O) :
    HasSum (fun k ↦ coeff k G * algebraMap O (FractionRing O) (π * u) ^ k)
      (algebraMap O (FractionRing O) (evalT u H)) := by
  have h1 : HasSum (fun k ↦ coeff k H * u ^ k) (evalT u H) :=
    (summable_mul_of_tendsto_zero hdec).hasSum
  refine (h1.map (algebraMap O (FractionRing O)) continuous_algebraMap).congr_fun fun k ↦ ?_
  simp only [Function.comp_apply, map_mul, map_pow, hGH k]
  ring

end Bridge

end PSeries

section DiskBound

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [IsTopologicalRing O]
  {π : O} {p e : ℕ} (hram : IsUniformizer π p e) (hpe : e + 1 < p)

include hram hpe in
/-- **The Coleman integral converges on a residue disk**: for `G` the antiderivative over the
fraction field of an integral disk expansion `W`, the series `G` sums at every parameter in the
maximal ideal. The value is the substituted antiderivative evaluated at `z/π`, which is what
makes it integral. -/
theorem exists_forall_hasSum_antideriv (W : O⟦X⟧) {G : PowerSeries (FractionRing O)}
    (hGW : G = antideriv (W.map (algebraMap O (FractionRing O)))) :
    ∃ A₀ : O → FractionRing O, ∀ z ∈ maximalIdeal O,
      HasSum (fun k ↦ coeff k G * algebraMap O (FractionRing O) z ^ k) (A₀ z) := by
  obtain ⟨H, hH, hGH⟩ := PSeries.exists_coeff_eq_of_antideriv hram hpe W hGW
  have hdvd : ∀ z ∈ maximalIdeal O, ∃ u, z = π * u := fun z hz ↦ hram.mem_iff.mp hz
  choose! u hu using hdvd
  refine ⟨fun z ↦ algebraMap O (FractionRing O) (PSeries.evalT (u z) H), fun z hz ↦ ?_⟩
  have hsum :=
    PSeries.hasSum_algebraMap_evalT (PSeries.tendsto_coeff_antideriv hram hpe hH) hGH (u z)
  rwa [← hu z hz] at hsum

variable [T2Space O] {m : ℕ}

include hram in
/-- **The per-disk bound** (blueprint `thm:disk-bound`): a set of points of one residue disk
at whose parameters `ζ P` the Coleman integral `G` takes one and the same value has at most
`1 + m` elements, where `m` is any index with a unit coefficient in the disk expansion `W`
of the differential (`m = ord_P_bar(ω_bar)` gives the sharpest bound) and `p > m + e + 1`.

The hypotheses that carry the geometry are that the parameters lie in the maximal ideal
(`hζ`) and are distinct (`hinj`); `hA` says that the integral takes the value `A P` at the
point `P`, and the constancy `hAconst` of those values is what blueprint `thm:glue` plus the
annihilating property of `ω` (blueprint `thm:annihilator`) provide, `A Q - A P` being `λ_ω`
of the difference of the two classes. -/
theorem disk_count_le (hord : m + e + 1 < p) {W : O⟦X⟧} (hmu : IsUnit (coeff m W))
    {G : PowerSeries (FractionRing O)}
    (hGW : G = antideriv (W.map (algebraMap O (FractionRing O))))
    {α : Type*} {S : Set α} (ζ : α → O) (hζ : ∀ P ∈ S, ζ P ∈ maximalIdeal O)
    (hinj : Set.InjOn ζ S) {A : α → FractionRing O}
    (hA : ∀ P ∈ S,
      HasSum (fun k ↦ coeff k G * algebraMap O (FractionRing O) (ζ P) ^ k) (A P))
    (hAconst : ∀ P ∈ S, ∀ Q ∈ S, A P = A Q) :
    S.encard ≤ 1 + m := by
  have hpe : e + 1 < p := by lia
  obtain ⟨H, hH, hGH⟩ := PSeries.exists_coeff_eq_of_antideriv hram hpe W hGW
  have hdvd (P : α) (hP : P ∈ S) : ∃ u, ζ P = π * u := hram.mem_iff.mp (hζ P hP)
  choose! u hu using hdvd
  have hinj' : Set.InjOn u S := fun P hP Q hQ h ↦
    hinj hP hQ (by rw [hu P hP, hu Q hQ, h])
  have hval (P : α) (hP : P ∈ S) : A P = algebraMap O (FractionRing O) (PSeries.evalT (u P) H) :=
    (hu P hP ▸ hA P hP).unique
      (PSeries.hasSum_algebraMap_evalT (PSeries.tendsto_coeff_antideriv hram hpe hH) hGH (u P))
  rw [add_comm]
  refine PSeries.encard_le_of_evalT_const hram hH hord hmu u hinj' fun P hP Q hQ ↦ ?_
  refine IsFractionRing.injective O (FractionRing O) ?_
  rw [← hval P hP, ← hval Q hQ]
  exact hAconst P hP Q hQ

end DiskBound

end ChabautyColeman

end
