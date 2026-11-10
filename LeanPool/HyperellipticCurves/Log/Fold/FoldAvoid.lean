/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.Resultant
public import LeanPool.HyperellipticCurves.Log.Fold.CuspInstance

import LeanPool.HyperellipticCurves.Log.Fold.FoldWitness

/-!
# The Weierstrass-avoidance numerators of the fold

The per-stage Weierstrass-avoidance conditions of the fold — `IsCoprime Uⱼ (2·Vⱼ)` for every
intermediate state of the `2g`-step fold, the fold form of `ChabautyColeman.IsPipelineAvoid` — as
*polynomial* conditions on curve tuples, ready for the avoidance engine.

The universal numerator of the stage-`j` condition is the formal-degree `(g, g)` resultant
of the `u`- and `v`-components of the universal numerator state
(`ChabautyColeman.univAvoidNum`). This file supplies the two inputs the descent
(`ChabautyColeman.aeval_family_ne_zero`) needs:

* **isobarity** (`ChabautyColeman.isWeightedHomogeneous_univAvoidNum`), via a general
  weight computation for resultants of isobaric polynomials
  (`ChabautyColeman.IsIsobaric.resultant`, from the graded-determinant lemma
  `ChabautyColeman.isWeightedHomogeneous_det` — both Mathlib-bound);
* **cuspidal nonvanishing** (`ChabautyColeman.cuspAvoidNum_ne_zero`): on the cusp the
  states of the generic fold have coprime components because their supports avoid `0`
  (`ChabautyColeman.isCoprime_of_dvd_sq_pow` at the witness clauses `Aⱼ(0) ≠ 0`), so the
  resultant of the denominator-scaled states is a nonzero multiple of a unit.

The engine instances of these numerators, the family refutation and the enlarged common
witness live in `LeanPool.HyperellipticCurves.Log.Fold.CenterFold`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### Weighted homogeneity of determinants and resultants -/

section DetWH

variable {R : Type*} [CommRing R] {σ : Type*} {M : Type*} [AddCommMonoid M] {w : σ → M}

/-- **A determinant with graded entries is weighted-homogeneous**: if the `(i, j)` entry
is weighted-homogeneous of weight `r i + c j`, the determinant is weighted-homogeneous of
`∑ r + ∑ c`. -/
theorem isWeightedHomogeneous_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MvPolynomial σ R)} {r c : ι → M}
    (h : ∀ i j, (A i j).IsWeightedHomogeneous w (r i + c j)) :
    A.det.IsWeightedHomogeneous w (∑ i, r i + ∑ i, c i) := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun p _ ↦ ?_
  have hprod : (∏ i, A (p i) i).IsWeightedHomogeneous w (∑ i, r i + ∑ i, c i) := by
    refine (MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ (fun i ↦ r (p i) + c i)
      fun i _ ↦ h (p i) i).of_weight_eq ?_
    rw [Finset.sum_add_distrib]
    exact congrArg (· + ∑ i, c i) (Equiv.sum_comp p r)
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rw [Units.neg_smul, one_smul]
    exact hprod.neg

end DetWH

section ResWH

variable {K : Type*} [CommRing K] {σ : Type*} {w : σ → ℤ}

/-- **The formal-degree resultant of isobaric polynomials is weighted-homogeneous**, of
weight `n·a + m·b - 2·m·n`. -/
theorem IsIsobaric.resultant {a b : ℤ} {f g : (MvPolynomial σ K)[X]}
    (hf : IsIsobaric w a f) (hg : IsIsobaric w b g) (m n : ℕ) :
    (f.resultant g m n).IsWeightedHomogeneous w (n * a + m * b - 2 * m * n) := by
  rw [Polynomial.resultant]
  have hent : ∀ i j, ((Polynomial.sylvester f g m n) i j).IsWeightedHomogeneous w
      ((fun i : Fin (m + n) ↦ (-2 : ℤ) * (i : ℕ)) i
        + (fun j ↦ Fin.addCases (fun j₁ : Fin m ↦ b + 2 * (j₁ : ℕ))
            (fun j₁ : Fin n ↦ a + 2 * (j₁ : ℕ)) j) j) := by
    intro i j
    induction j using Fin.addCases with
    | left j₁ =>
      rw [Polynomial.sylvester]
      simp only [Matrix.of_apply, Fin.addCases_left]
      split_ifs with hin
      · rw [Set.mem_Icc] at hin
        exact (hg _).of_weight_eq (by rw [Nat.cast_sub hin.1]; ring)
      · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
    | right j₁ =>
      rw [Polynomial.sylvester]
      simp only [Matrix.of_apply, Fin.addCases_right]
      split_ifs with hin
      · rw [Set.mem_Icc] at hin
        exact (hf _).of_weight_eq (by rw [Nat.cast_sub hin.1]; ring)
      · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  refine (isWeightedHomogeneous_det hent).of_weight_eq ?_
  -- the weight arithmetic: `∑ i, (-2 i) + (∑ c) = n·a + m·b - 2·m·n`
  have hsplit : ∑ i ∈ Finset.range (m + n), (i : ℤ)
      = (∑ i ∈ Finset.range m, (i : ℤ)) + ((∑ i ∈ Finset.range n, (i : ℤ)) + m * n) := by
    rw [Finset.sum_range_add]
    push_cast
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h1 : ∑ i : Fin (m + n), (-2 : ℤ) * ((i : ℕ) : ℤ)
      = -2 * ∑ i ∈ Finset.range (m + n), (i : ℤ) := by
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i ↦ (i : ℤ)) (m + n)]
  have h2 : ∑ j : Fin (m + n), Fin.addCases (fun j₁ : Fin m ↦ b + 2 * ((j₁ : ℕ) : ℤ))
      (fun j₁ : Fin n ↦ a + 2 * ((j₁ : ℕ) : ℤ)) j
      = ((m : ℤ) * b + 2 * ∑ i ∈ Finset.range m, (i : ℤ))
        + ((n : ℤ) * a + 2 * ∑ i ∈ Finset.range n, (i : ℤ)) := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ (i : ℤ)) m,
      Fin.sum_univ_eq_sum_range (fun i ↦ (i : ℤ)) n]
  rw [h1, h2, hsplit]
  ring

end ResWH

/-! ### The universal avoidance numerators -/

section Univ

variable {K : Type*} [CommRing K] {g : ℕ}

variable (g) in
/-- **The weight of the stage-`j` avoidance numerator**: the resultant weight of the
scaled state components at formal degrees `(g, g)`. -/
def foldAvoidWt (ω₀ : ℤ) (j : ℕ) : ℤ := g * (2 * foldWt g ω₀ j + 2 * g + 1)

variable (K g) in
/-- **The universal Weierstrass-avoidance numerators** of the fold: the formal-degree
`(g, g)` resultant of the `u`- and `v`-components of the universal numerator state at
stage `j`. Nonvanishing at a specialization makes the honest state's components coprime —
the per-stage Weierstrass-avoidance condition of the fold. -/
noncomputable def univAvoidNum (j : ℕ) : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K :=
  ((foldNum (univF K g) (univXs K g) (univYs K g) (univBase K g) j).u).resultant
    ((foldNum (univF K g) (univXs K g) (univYs K g) (univBase K g) j).v) g g

/-- **Isobarity of the universal avoidance numerators.** -/
theorem isWeightedHomogeneous_univAvoidNum [IsDomain K] (j : ℕ) :
    (univAvoidNum K g j).IsWeightedHomogeneous (univWt g)
      (foldAvoidWt g (4 * g * ((g : ℤ) - 1)) j) := by
  have hstate : IsIsobaricState (univWt g) g
      (foldNum (univF K g) (univXs K g) (univYs K g) (univBase K g) j)
      (foldWt g (4 * g * ((g : ℤ) - 1)) j) :=
    isIsobaricState_foldNum isIsobaric_univF isWeightedHomogeneous_univXs
      isWeightedHomogeneous_univYs isIsobaricState_univBase j
  exact (hstate.u_iso.resultant hstate.v_iso g g).of_weight_eq (by rw [foldAvoidWt]; ring)

end Univ

/-! ### Cuspidal nonvanishing of the avoidance numerators -/

section Cusp

/-- On the cuspidal model `y² = X^N`, a Mumford state whose support avoids `0` has
coprime components. -/
theorem isCoprime_of_dvd_sq_pow {F : Type*} [Field F] {U V : F[X]} {N : ℕ}
    (hdvd : U ∣ V ^ 2 - X ^ N) (h0 : U.eval 0 ≠ 0) : IsCoprime U V := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hunit
  have hgU : EuclideanDomain.gcd U V ∣ U := EuclideanDomain.gcd_dvd_left U V
  have hgN : EuclideanDomain.gcd U V ∣ X ^ N := by
    have h1 : EuclideanDomain.gcd U V ∣ V ^ 2 - X ^ N := hgU.trans hdvd
    have h2 : EuclideanDomain.gcd U V ∣ V ^ 2 :=
      (EuclideanDomain.gcd_dvd_right U V).mul_left V |>.trans (by rw [sq])
    exact (dvd_sub h2 h1).trans (by rw [sub_sub_cancel])
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X N).mp hgN
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact hunit (associated_one_iff_isUnit.mp (by simpa using hassoc))
  · obtain ⟨q, hq⟩ := ((dvd_pow_self X hi0.ne').trans hassoc.symm.dvd).trans hgU
    rw [hq] at h0
    simp at h0

variable {k : Type*} [Field k] {g : ℕ}

/-- The states of the generic cuspidal fold have coprime components: their supports avoid
`0` by the witness clauses. -/
private theorem isCoprime_foldChain_gen [NeZero (2 : k)] (hg2 : 2 ≤ g) {j : ℕ}
    (hj : j ≤ 2 * g) :
    IsCoprime
      (foldChain (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
        (foldGenH (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
          (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1)) (genU₀ k g) (genV₀ k g))
        (genU₀ k g) (genV₀ k g) j).1
      (foldChain (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
        (foldGenH (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
          (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1)) (genU₀ k g) (genV₀ k g))
        (genU₀ k g) (genV₀ k g) j).2 := by
  have hg : 0 < g := by lia
  obtain ⟨H₀, hwit⟩ := exists_genCuspFold_witness (k := k) hg2
  have hH := genFoldH_eq_foldGenH hg ((hwit 0 (by lia)).2.2.1 (by lia))
  have h1 := (cuspChain_eq_foldChain (U₀ := genU₀ k g) (V₀ := genV₀ k g)
    (H := genFoldH k g H₀) g (genA₀ k g) (foldNodes g (genNode k)) j).trans
      (foldChain_congr_H fun i _ ↦ hH i)
  rw [← h1]
  have hs := (hwit j hj).1
  have hA0 := (hwit j hj).2.1
  have hU0 : ((genCuspFold k g H₀ j).1).eval 0 ≠ 0 := by
    have h := hs.eval_sq 0
    rw [show ((0 : FractionRing (MvPolynomial ℕ k)) ^ 2) = 0 by ring] at h
    rw [h, neg_zero]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (mul_ne_zero hA0 hA0)
  exact isCoprime_of_dvd_sq_pow hs.dvd_sq hU0

/-- **The cuspidal avoidance numerators are nonzero**: the cusp specialization of each
universal avoidance numerator is a nonzero polynomial — the second input the descent
needs for the per-stage coprimality conditions. -/
theorem cuspAvoidNum_ne_zero [NeZero (2 : k)] (hg2 : 2 ≤ g) {j : ℕ} (hj : j ≤ 2 * g) :
    MvPolynomial.aeval (cuspSpec k g) (univAvoidNum k g j) ≠ 0 := by
  have hg : 0 < g := by lia
  -- map everything into the fraction field in one composite step
  set ψ : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) k
      →+* FractionRing (MvPolynomial ℕ k) :=
    ((algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))).comp
      (MvPolynomial.rename (Fin.val : Fin g → ℕ)).toRingHom).comp
      (MvPolynomial.aeval (cuspSpec k g)).toRingHom with hψdef
  suffices h : ψ (univAvoidNum k g j) ≠ 0 by
    intro h0
    refine h ?_
    rw [hψdef, RingHom.comp_apply]
    have h0' : (MvPolynomial.aeval (cuspSpec k g)).toRingHom (univAvoidNum k g j) = 0 := h0
    rw [h0', map_zero]
  -- the composite sends the universal inputs to the generic cuspidal ones
  have hψx : ∀ i : Fin g, ψ (MvPolynomial.X (.inl i)) = genNode k i ^ 2 := fun i ↦ by
    simp [hψdef, cuspSpec, genNode]
  have hψy : ∀ i : Fin g, ψ (MvPolynomial.X (.inr (.inl i))) = genNode k i ^ (2 * g + 1) :=
    fun i ↦ by simp [hψdef, cuspSpec, genNode]
  have hF : (univF k g).map ψ = X ^ (2 * g + 1) := by
    rw [univF, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Finset.sum_eq_zero fun r _ ↦ by simp [hψdef, cuspSpec],
      add_zero]
  have hB : (univBase k g).map ψ
      = foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
        fun i ↦ genNode k i ^ (2 * g + 1) := by
    rw [univBase, map_foldBase, hF]
    congr 1 <;> funext i
    · exact hψx i
    · exact hψy i
  have hstate : (foldNum (univF k g) (univXs k g) (univYs k g) (univBase k g) j).map ψ
      = foldNum (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
        (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1))
        (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
          fun i ↦ genNode k i ^ (2 * g + 1)) j := by
    rw [map_foldNum, hF, hB]
    rw [show (fun i ↦ ψ (univXs k g i)) = foldXs fun i : Fin g ↦ genNode k i ^ 2 from
      _root_.funext fun i ↦ by
        rw [univXs_eq_foldXs, map_foldXs]
        exact congrFun (congrArg _ (_root_.funext hψx)) i]
    rw [show (fun i ↦ ψ (univYs k g i))
        = foldYs fun i : Fin g ↦ genNode k i ^ (2 * g + 1) from
      _root_.funext fun i ↦ by
        rw [univYs_eq_foldYs, map_foldYs]
        exact congrFun (congrArg _ (_root_.funext hψy)) i]
    refine foldNum_congr (fun i hi ↦ ?_) fun i hi ↦ ?_
    · rw [foldXs, foldNodes]
      split_ifs with h1 h2
      · rfl
      · rw [neg_sq, Fin.val_rev, Fin.val_mk,
          show g - (i - g + 1) = g - 1 - (i - g) by lia]
      · exact absurd (by lia) h2
    · rw [foldYs, foldNodes]
      split_ifs with h1 h2
      · rfl
      · rw [Odd.neg_pow ⟨g, by ring⟩, Fin.val_rev, Fin.val_mk,
          show g - (i - g + 1) = g - 1 - (i - g) by lia]
      · exact absurd (by lia) h2
  -- the image of the resultant is the resultant of the scaled generic states
  rw [univAvoidNum, ← Polynomial.resultant_map_map _ _ g g ψ]
  have hu := congrArg MumfordNum.u hstate
  have hv := congrArg MumfordNum.v hstate
  rw [MumfordNum.map_u] at hu
  rw [MumfordNum.map_v] at hv
  rw [hu, hv]
  -- identify the scaled state with the honest one and peel the denominators
  have hbaseS := isScaledState_foldBase_gen (k := k) (g := g)
  have hcurve : ∀ i < j, (foldNodes g (genNode k) i ^ (2 * g + 1)) ^ 2
      = (X ^ (2 * g + 1) : (FractionRing (MvPolynomial ℕ k))[X]).eval
        (foldNodes g (genNode k) i ^ 2) := fun i _ ↦ by
    rw [eval_pow, eval_X, ← pow_mul, ← pow_mul, mul_comm (2 * g + 1) 2]
  have hT0 : foldNodes g (genNode k) 0 = genNode k 0 := foldNodes_of_lt hg
  have hx₀ : (genU₀ k g).eval (foldNodes g (genNode k) 0 ^ 2) = 0 := by
    rw [hT0]
    exact eval_tupleU_self (fun i : Fin g ↦ genNode k i ^ 2) ⟨0, hg⟩
  have hV₀ : (genV₀ k g).eval (foldNodes g (genNode k) 0 ^ 2)
      = foldNodes g (genNode k) 0 ^ (2 * g + 1) := by
    rw [hT0]
    exact eval_tupleV genNode_sq_injective ⟨0, hg⟩
  have hc : ∀ i < j, foldCondNum (X ^ (2 * g + 1))
      (fun i ↦ foldNodes g (genNode k) i ^ 2)
      (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1))
      (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
        fun i ↦ genNode k i ^ (2 * g + 1)) i ≠ 0 :=
    fun i hi ↦ foldCondNum_cusp_ne_zero hg2 (by lia)
  have hspec := isScaledState_foldNum (monic_X_pow _) (natDegree_X_pow _) hbaseS hx₀ hV₀
    hcurve hc
  rw [hspec.u_eq, hspec.v_eq, Polynomial.resultant_C_mul_left,
    Polynomial.resultant_C_mul_right]
  have hden := hspec.den_ne
  refine mul_ne_zero (pow_ne_zero _ hden) (mul_ne_zero (pow_ne_zero _ hden) ?_)
  -- the honest resultant is a unit: monic support of the right degree, coprime pair
  have hUdeg := hspec.state.natDegree_U
  have hres := isUnit_resultant_of_isCoprime hspec.state.monicU
    (natDegree_le_iff_degree_le.mpr hspec.state.degree_V.le)
    (isCoprime_foldChain_gen hg2 hj)
  rw [hUdeg] at hres
  exact hres.ne_zero

end Cusp

end ChabautyColeman

end
