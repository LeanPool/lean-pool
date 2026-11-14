/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
public import LeanPool.HyperellipticCurves.Series.FormalGroupLaw.Invariance
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

import LeanPool.HyperellipticCurves.ForMathlib.PadicValNat
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The formal logarithm of a formal group law

Over a field `K`, the formal logarithm `ChabautyColeman.FormalGroupLaw.log` is the radial
(Euler) antiderivative `ChabautyColeman.eulerAntideriv` of the row `∑_j (M⁻¹)_{ij} X_j` of the
invariant differential. That `log`'s differential is the invariant differential (`pderiv_log`)
uses the closedness proved in `LeanPool.HyperellipticCurves.Series.FormalGroupLaw.Invariance`
together with
`CharZero`. Over a local ring of residue characteristic `p`, `coeff_log_map_padic` bounds the
denominators of the coefficients by powers of `p`, and `coeff_log_map_scale` /
`exists_integral_scaled_log` turn that into integrality after scaling the variables by a
uniformizer `π` with `p ∣ π ^ e` and `p > e + 1` (`IsUniformizer π p e`).
(The formal exponential — the compositional inverse of `log` — is formalized in
`upstream HyperellipticCurves.Archive.FormalGroupExp`; the main theorems do not depend on it, since
they use
the logarithm only as a homomorphism, never its injectivity.)

## Main definitions
* `ChabautyColeman.eulerAntideriv`: the radial antiderivative (divide the degree-`k` part by `k`).
* `ChabautyColeman.FormalGroupLaw.log`.

## Main statements
* `ChabautyColeman.FormalGroupLaw.pderiv_log`, `.log_subst_F`: the differential of `log`.
* `ChabautyColeman.FormalGroupLaw.exists_integral_scaled_log`: the `π`-scaled integral logarithm.

Blueprint nodes: `def:fgl-log`, `lem:fgl-log-diff`.
-/

@[expose] public section

open MvPowerSeries IsLocalRing Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace ChabautyColeman
/-! ### The radial (Euler) antiderivative -/

section euler

variable {ι K : Type*} [DivisionRing K]

/-- The radial (Euler) antiderivative of a multivariate power series: divide the
degree-`k` homogeneous part by `k`. (At `k = 0` the junk value `(0 : K)⁻¹ = 0` kills
the constant term, as intended.) -/
noncomputable def eulerAntideriv (g : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun d ↦ (d.degree : K)⁻¹ * MvPowerSeries.coeff d g

theorem coeff_eulerAntideriv (g : MvPowerSeries ι K) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (eulerAntideriv g)
      = (d.degree : K)⁻¹ * MvPowerSeries.coeff d g := rfl

@[simp]
theorem constantCoeff_eulerAntideriv (g : MvPowerSeries ι K) :
    constantCoeff (eulerAntideriv g) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_eulerAntideriv]
  simp

end euler

namespace FormalGroupLaw

/-! ### The formal logarithm and exponential -/

section log

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Φ : FormalGroupLaw K ι)

/-- The formal logarithm of a formal group law over a field: the radial antiderivative of the
row `∑_j (M⁻¹)_{ij} X_j` of the invariant differential. Characteristic zero is needed not
here but for the defining property `ChabautyColeman.FormalGroupLaw.pderiv_log`, that its
differential is the invariant differential, which is proved with the invariance identities. -/
noncomputable def log (i : ι) : MvPowerSeries ι K :=
  eulerAntideriv (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)

@[simp]
theorem constantCoeff_log (i : ι) : constantCoeff (Φ.log i) = 0 :=
  constantCoeff_eulerAntideriv _

-- `∂_k` of the invariant differential row, rewritten with closedness
private lemma pderiv_log_row (i k : ι) :
    pderiv k (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)
      = (∑ j, MvPowerSeries.X j * pderiv j (Φ.diffMatrix⁻¹ i k)) + Φ.diffMatrix⁻¹ i k := by
  rw [map_sum]
  have hterm (j : ι) : pderiv k (Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)
      = MvPowerSeries.X j * pderiv j (Φ.diffMatrix⁻¹ i k)
        + if j = k then Φ.diffMatrix⁻¹ i j else 0 := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_X,
      Φ.pderiv_diffMatrixInv_symm i j k, add_comm]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ k fun j ↦ Φ.diffMatrix⁻¹ i j,
    ite_eq_left (Finset.mem_univ k)]

variable [CharZero K]

/-- The differential of the formal logarithm is the invariant differential:
`∂_k Λ_i = (M⁻¹)_{ik}`. This is where characteristic zero is used: the Euler operator
plus one is invertible on coefficients. -/
theorem pderiv_log (i k : ι) :
    pderiv k (Φ.log i) = Φ.diffMatrix⁻¹ i k := by
  ext d
  have hdeg : (d + Finsupp.single k 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hn : ((d.degree + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr d.degree.succ_ne_zero
  have hkey := congrArg (coeff (R := K) d) (pderiv_log_row Φ i k)
  rw [map_add, coeff_pderiv, coeff_sum_X_mul_pderiv] at hkey
  rw [coeff_pderiv, log, coeff_eulerAntideriv, hdeg, mul_assoc, hkey,
    show ((d.degree : ℕ) : K) * coeff d (Φ.diffMatrix⁻¹ i k) + coeff d (Φ.diffMatrix⁻¹ i k)
        = ((d.degree + 1 : ℕ) : K) * coeff d (Φ.diffMatrix⁻¹ i k) by push_cast; ring,
    inv_mul_cancel_left₀ hn]

-- `∂/∂Y_k` of both sides of the additivity identity agree
private lemma pderiv_inr_log_subst (i k : ι) :
    pderiv (Sum.inr k) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i))
      = pderiv (Sum.inr k)
          (MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
              (Φ.log i)
            + MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
              (Φ.log i)) := by
  have hsum : pderiv (Sum.inr k) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i))
      = ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
          * pderiv (Sum.inr k) (Φ.F a) := by
    rw [pderiv_subst (hasSubst_F Φ)]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Φ.pderiv_log i a]
  rw [map_add, hsum, diffMatrixInv_subst_F Φ i k, pderiv_Yemb, Φ.pderiv_log i k,
    pderiv_subst_eq_zero hasSubst_Xemb (Sum.inr k) (fun _ ↦ by simp) (Φ.log i), zero_add]

-- `∂/∂X_k` of both sides of the additivity identity agree
private lemma pderiv_inl_log_subst (i k : ι) :
    pderiv (Sum.inl k) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i))
      = pderiv (Sum.inl k)
          (MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
              (Φ.log i)
            + MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
              (Φ.log i)) := by
  have hsum : pderiv (Sum.inl k) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i))
      = ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
          * pderiv (Sum.inl k) (Φ.F a) := by
    rw [pderiv_subst (hasSubst_F Φ)]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Φ.pderiv_log i a]
  rw [map_add, hsum, diffMatrixInv_subst_F_inl Φ i k, pderiv_Xemb, Φ.pderiv_log i k,
    pderiv_subst_eq_zero hasSubst_Yemb (Sum.inl k) (fun _ ↦ by simp) (Φ.log i), add_zero]

/-- The formal logarithm is additive on the formal group law:
`Λ(F(X,Y)) = Λ(X) + Λ(Y)` as formal power series in the two blocks of variables. -/
theorem log_subst_F (i : ι) :
    MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i)
      = MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
          (Φ.log i)
        + MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
          (Φ.log i) := by
  refine pderiv.ext (fun s ↦ ?_) ?_
  · rcases s with k | k
    · exact pderiv_inl_log_subst Φ i k
    · exact pderiv_inr_log_subst Φ i k
  · rw [map_add,
      MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero (hasSubst_F Φ)
        (fun j ↦ Φ.zero_constantCoeff j),
      MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero hasSubst_Xemb (fun s ↦ by simp),
      MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero hasSubst_Yemb (fun s ↦ by simp),
      constantCoeff_log]
    ring

end log

/-! ### Base change of the logarithm; p-adic denominator bounds -/

section logBaseChange

variable {O K : Type*} [CommRing O] [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Φ : FormalGroupLaw O ι)

-- the integral row `∑_j (M⁻¹)_{ij} X_j` base-changes to the row over `K`
private lemma map_log_row (f : O →+* K) (i : ι) :
    MvPowerSeries.map f (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)
      = ∑ j, (Φ.map f).diffMatrix⁻¹ i j * MvPowerSeries.X j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, MvPowerSeries.map_X, Φ.diffMatrixInv_map f, Matrix.map_apply]

/-- The coefficients of the logarithm of a base-changed formal group law: the numerator
`f (coeff_d (∑_j (M⁻¹)_{ij} X_j))` is integral (in the image of `f`), and the only
denominator is the total degree `deg d`. This is the "denominator bookkeeping" behind
convergence of the logarithm. -/
theorem coeff_log_map (f : O →+* K) (i : ι) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d ((Φ.map f).log i)
      = (d.degree : K)⁻¹ * f (MvPowerSeries.coeff d (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j))
      := by
  rw [log, coeff_eulerAntideriv, ← Φ.map_log_row f, coeff_map]

variable [IsLocalRing O] {π : O} {p e : ℕ}

/-- The `p`-power denominator bound for the logarithm of a base-changed formal group law
over a local ring of residue characteristic `p`: multiplying the degree-`d` coefficient by
`f(p)^(v_p(deg d))` clears the denominator, landing in the image of `f`. So the only
denominators are powers of `p`, with exponent `v_p(deg d)`. -/
theorem coeff_log_map_padic (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O)
    (f : O →+* K) (hfp : f (p : O) ≠ 0) (i : ι) (d : ι →₀ ℕ) :
    ∃ c : O, f (p : O) ^ (padicValNat p d.degree)
      * MvPowerSeries.coeff d ((Φ.map f).log i) = f c := by
  rw [Φ.coeff_log_map f]
  set k := d.degree
  set cd := MvPowerSeries.coeff d (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · exact ⟨0, by simp [hk0]⟩
  obtain ⟨u, hu⟩ := exists_units_natCast_eq hp hpmem hkpos.ne'
  refine ⟨(↑u⁻¹ : O) * cd, ?_⟩
  have hkK : (k : K) = f (p : O) ^ padicValNat p k * f (↑u : O) := by
    rw [← map_natCast f k, hu, map_mul, map_pow]
  have hbne : f (↑u : O) ≠ 0 := (u.isUnit.map f).ne_zero
  have hfu : (f (↑u : O))⁻¹ = f (↑u⁻¹ : O) :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, map_one])
  rw [map_mul, ← hfu, hkK]
  field_simp

/-- **The `π`-scaled logarithm has integral coefficients**, with the growing power of the
maximal ideal made explicit: scaling the variables by a uniformizer `π` clears the
`p`-power denominator of `coeff_d Λ` and leaves the value in `𝔪 ^ (deg d - e·v_p(deg d))`.
So substituting `X_j ↦ π·U_j` lands the logarithm in `O⟦U⟧`, and the exponent
`deg d - e·v_p(deg d) → ∞` drives convergence on `𝔪^n`. -/
theorem coeff_log_map_scale (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (f : O →+* K) (hfp : f (p : O) ≠ 0) (i : ι) (d : ι →₀ ℕ) :
    ∃ c ∈ maximalIdeal O ^ (d.degree - e * padicValNat p d.degree),
      f π ^ d.degree * MvPowerSeries.coeff d ((Φ.map f).log i) = f c := by
  obtain ⟨b, hb⟩ := Φ.coeff_log_map_padic hram.prime hram.natCast_mem f hfp i d
  obtain ⟨c, hcmem, hcv⟩ := hram.exists_pow_eq (v := padicValNat p d.degree)
    (k := d.degree)
    (by have := Nat.mul_padicValNat_le hpe d.degree; lia)
  refine ⟨c * b, Ideal.mul_mem_right _ _ hcmem, ?_⟩
  rw [map_mul, ← hb, ← map_pow, hcv, map_mul, map_pow]
  ring

end logBaseChange

/-! ### The π-scaled integral logarithm -/

section logConvergence

variable {O K : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (Φ : FormalGroupLaw O ι) {π : O} {p e : ℕ}

/-- Convergence of the logarithm on `𝔪^n`: after scaling the variables by a uniformizer
`π`, the logarithm of the base change `f_*Φ` descends to a power series `H` with
coefficients in `O` that tend to `0`. Concretely `H` is the integral form of `Λ(πU)`: its
base change is the `π`-scaled logarithm (`f (coeff_d H) = f(π)^{deg d} · coeff_d Λ`) and its
coefficients lie in growing powers of `𝔪`, so `H` — hence `Λ` on `𝔪^n` via `evalT` —
converges. The ramification bound enters only through `p > e + 1`, which keeps the
`p`-power denominators below the `π`-power gained. -/
theorem exists_integral_scaled_log (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (f : O →+* K) (hfp : f (p : O) ≠ 0) (i : ι) :
    ∃ H : MvPowerSeries ι O,
      (∀ d, f (coeff d H) = f π ^ d.degree * coeff d ((Φ.map f).log i)) ∧
      Tendsto (fun d ↦ coeff d H) cofinite (𝓝 0) := by
  choose b hb1 hb2 using Φ.coeff_log_map_scale hram hpe f hfp i
  exact ⟨b, fun d ↦ (hb2 d).symm, MvPSeries.tendsto_coeff_zero_of_mem_pow hb1
    ((Nat.tendsto_sub_mul_padicValNat_atTop hpe).comp Finsupp.tendsto_degree_cofinite)⟩

end logConvergence

end FormalGroupLaw

end ChabautyColeman

end
