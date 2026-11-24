/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateWedgeFamily

/-!
# The Pfaffian-type formula for a mixed exterior product

`FirstPass.StandardKahlerTopPower.coordinateWedgePower_apply_eq_pairingSum` evaluates the
`k`-fold exterior power of ONE real two-form as a signed permutation sum,
`A^{∧k}(v) = 2⁻ᵏ ∑_σ sign σ ∏_{i<k} A(v_{σ(q(i,0))}, v_{σ(q(i,1))})`.

Here the same formula is proved for `coordinateWedgeFamily`, the exterior product of `k`
possibly DIFFERENT two-forms: the `i`-th factor of the product reads off `A i`.  Nothing in
the original argument used that the form was the same in every factor.

Two consequences are read off the formula and are what the mixed density identity
(`fpmma:geometric-density`) needs, neither of which is visible from the recursive
definition:

* **multilinearity in each slot** — `A i` occurs exactly once in every summand;
* **symmetry** — permuting the slots by `τ` reindexes the product by `τ⁻¹` and the
  permutation sum by the induced block permutation of `Fin k × Fin 2`, whose sign is
  `(sign τ)² = 1` because the blocks have even size.  This is the precise form of
  "two-forms commute".
-/

@[expose] public section

noncomputable section

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- The Pfaffian-type sum of a two-form over all permutations of an index type
`ι`, where `q` picks out `k` ordered pairs of indices. -/
def coordinatePairingSum {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : CoordinateRealTwoForm n) (q : Fin k × Fin 2 → ι) (v : ι → ComplexModel n) : ℝ :=
  ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∏ i : Fin k, A ![v (σ (q (i, 0))), v (σ (q (i, 1)))]

theorem coordinatePairingSum_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {k : ℕ}
    (A : CoordinateRealTwoForm n) (e : ι ≃ κ) (q : Fin k × Fin 2 → ι)
    (v : κ → ComplexModel n) :
    coordinatePairingSum A (e ∘ q) v = coordinatePairingSum A q (v ∘ e) := by
  unfold coordinatePairingSum
  refine (Equiv.sum_comp (e.permCongr) _).symm.trans ?_
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Equiv.permCongr_apply]

theorem twoForm_apply_eq (A : CoordinateRealTwoForm n) (v : Fin 2 → ComplexModel n) :
    A v = A ![v 0, v 1] := by
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The Pfaffian-type sum of a FAMILY of two-forms over all permutations of an index type
`ι`, where `q` picks out `k` ordered pairs of indices and the `i`-th pair is tested against
`A i`.  For a constant family this is `coordinatePairingSum`. -/
def coordinatePairingSumFamily {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : Fin k → CoordinateRealTwoForm n) (q : Fin k × Fin 2 → ι) (v : ι → ComplexModel n) : ℝ :=
  ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∏ i : Fin k, A i ![v (σ (q (i, 0))), v (σ (q (i, 1)))]

theorem coordinatePairingSumFamily_const {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : CoordinateRealTwoForm n) (q : Fin k × Fin 2 → ι) (v : ι → ComplexModel n) :
    coordinatePairingSumFamily (fun _ => A) q v = coordinatePairingSum A q v := rfl

theorem coordinatePairingSumFamily_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {k : ℕ}
    (A : Fin k → CoordinateRealTwoForm n) (e : ι ≃ κ) (q : Fin k × Fin 2 → ι)
    (v : κ → ComplexModel n) :
    coordinatePairingSumFamily A (e ∘ q) v = coordinatePairingSumFamily A q (v ∘ e) := by
  unfold coordinatePairingSumFamily
  refine (Equiv.sum_comp (e.permCongr) _).symm.trans ?_
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Equiv.permCongr_apply]

/-- The successor step: wedging a form already given by a family pairing sum with one more
two-form gives the family pairing sum with one more factor. -/
theorem coordinateWedgeFamily_step_eq_pairingSum {j : ℕ}
    (A : Fin (j + 1) → CoordinateRealTwoForm n)
    (P : (ComplexModel n) [⋀^Fin (j * 2)]→L[ℝ] ℝ)
    (hP : ∀ u, P u = ((2 : ℝ) ^ j)⁻¹ *
      coordinatePairingSumFamily (fun i => A i.castSucc)
        (finProdFinEquiv : Fin j × Fin 2 → Fin (j * 2)) u)
    (v : Fin ((j + 1) * 2) → ComplexModel n) :
    coordinateWedge P (A (Fin.last j)) (v ∘ Fin.cast (show j * 2 + 2 = (j + 1) * 2 by ring)) =
      ((2 : ℝ) ^ (j + 1))⁻¹ *
        coordinatePairingSumFamily A
          (finProdFinEquiv : Fin (j + 1) × Fin 2 → Fin ((j + 1) * 2)) v := by
  have h : j * 2 + 2 = (j + 1) * 2 := by ring
  set e : Fin (j * 2) ⊕ Fin 2 ≃ Fin ((j + 1) * 2) := finSumFinEquiv.trans (finCongr h) with he
  set q : Fin (j + 1) × Fin 2 → Fin (j * 2) ⊕ Fin 2 := fun x =>
    Fin.lastCases (Sum.inr x.2) (fun i => Sum.inl (finProdFinEquiv (i, x.2))) x.1 with hq
  have hfp : (finProdFinEquiv : Fin (j + 1) × Fin 2 → Fin ((j + 1) * 2)) = e ∘ q := by
    funext x
    obtain ⟨x, b⟩ := x
    induction x using Fin.lastCases with
    | last => ext; simp [e, q, finProdFinEquiv]; ring
    | cast i => ext; simp [e, q, finProdFinEquiv]
  rw [hfp, coordinatePairingSumFamily_equiv, coordinateWedge_apply, coordinateWedgeSum_apply]
  have hwe : (v ∘ Fin.cast h) ∘ finSumFinEquiv = v ∘ e := rfl
  rw [hwe]
  set w : Fin (j * 2) ⊕ Fin 2 → ComplexModel n := v ∘ e with hw
  clear_value w q
  set F : Equiv.Perm (Fin (j * 2) ⊕ Fin 2) → ℝ := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∏ i : Fin (j + 1), A i ![w (σ (q (i, 0))), w (σ (q (i, 1)))] with hF
  have key : ∀ τ : Equiv.Perm (Fin (j * 2) ⊕ Fin 2),
      ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          (P (w ∘ ⇑τ ∘ Sum.inl) * A (Fin.last j) (w ∘ ⇑τ ∘ Sum.inr)) =
        ((2 : ℝ) ^ j)⁻¹ * ∑ ρ : Equiv.Perm (Fin (j * 2)), F (τ * Equiv.Perm.sumCongr ρ 1) := by
    intro τ
    rw [hP, coordinatePairingSumFamily, twoForm_apply_eq (A (Fin.last j))]
    simp only [hF, Finset.mul_sum, Finset.sum_mul, Fin.prod_univ_castSucc, hq,
      Fin.lastCases_castSucc, Fin.lastCases_last, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_sumCongr, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.Perm.coe_one, id,
      map_one, mul_one, Units.val_mul, Int.cast_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  simp only [key, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ ρ : Equiv.Perm (Fin (j * 2)),
      ∑ x : Equiv.Perm (Fin (j * 2) ⊕ Fin 2), F (x * ρ.sumCongr 1) = ∑ x, F x :=
    fun ρ => Equiv.sum_comp (Equiv.mulRight (Equiv.Perm.sumCongr ρ 1)) F
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have hS : coordinatePairingSumFamily A q w = ∑ x, F x := rfl
  rw [hS, Nat.factorial_two, pow_succ]
  have : ((j * 2).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **Pfaffian-type formula for a mixed exterior product.**  The exterior product of `k`
real two-forms is the signed permutation sum in which the `i`-th factor tests `A i`. -/
theorem coordinateWedgeFamily_apply_eq_pairingSum (k : ℕ)
    (A : Fin k → CoordinateRealTwoForm n) (v : Fin (k * 2) → ComplexModel n) :
    coordinateWedgeFamily k A v = ((2 : ℝ) ^ k)⁻¹ *
      coordinatePairingSumFamily A (finProdFinEquiv : Fin k × Fin 2 → Fin (k * 2)) v := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
      simp [coordinatePairingSumFamily, coordinateWedgeFamily, coordinateWedgeUnit]
    | 1, _ =>
      have hterm : ∀ σ : Equiv.Perm (Fin (1 * 2)), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i : Fin 1, A i ![v (σ (finProdFinEquiv (i, 0))), v (σ (finProdFinEquiv (i, 1)))] =
            A 0 v := by
        intro σ
        rw [Fin.prod_univ_one]
        have hv : A 0 ![v (σ (finProdFinEquiv ((0 : Fin 1), (0 : Fin 2)))),
            v (σ (finProdFinEquiv ((0 : Fin 1), (1 : Fin 2))))] = A 0 (v ∘ σ) := by
          rw [twoForm_apply_eq (A 0) (v ∘ σ)]
          rfl
        rw [hv, ← (A 0).coe_toAlternatingMap, AlternatingMap.map_perm, Units.smul_def,
          zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
        simp
      simp only [coordinatePairingSumFamily, hterm, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      change A 0 v = _
      ring
    | k + 2, ih =>
      rw [coordinateWedgeFamily_add_two_apply]
      exact coordinateWedgeFamily_step_eq_pairingSum A _
        (fun u => by
          have := ih (k + 1) (by omega) (fun i => A i.castSucc) u
          simpa using this) v

/-! ## Multilinearity in each slot

`A i` occurs exactly once in every summand of the pairing sum, so additivity and
`ℝ`-homogeneity in each slot are immediate. -/

section Multilinear

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [DecidableEq (Fin k)]

theorem coordinatePairingSumFamily_update_add (A : Fin k → CoordinateRealTwoForm n)
    (i : Fin k) (x y : CoordinateRealTwoForm n) (q : Fin k × Fin 2 → ι)
    (v : ι → ComplexModel n) :
    coordinatePairingSumFamily (Function.update A i (x + y)) q v =
      coordinatePairingSumFamily (Function.update A i x) q v +
        coordinatePairingSumFamily (Function.update A i y) q v := by
  unfold coordinatePairingSumFamily
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hprod : ∀ c : CoordinateRealTwoForm n,
      ∏ j : Fin k, (Function.update A i c) j ![v (σ (q (j, 0))), v (σ (q (j, 1)))] =
        c ![v (σ (q (i, 0))), v (σ (q (i, 1)))] *
          ∏ j ∈ Finset.univ \ {i}, A j ![v (σ (q (j, 0))), v (σ (q (j, 1)))] := by
    intro c
    rw [← Finset.prod_update_of_mem (Finset.mem_univ i)
      (fun j : Fin k => A j ![v (σ (q (j, 0))), v (σ (q (j, 1)))])
      (c ![v (σ (q (i, 0))), v (σ (q (i, 1)))])]
    exact Finset.prod_congr rfl fun j _ =>
      Function.apply_update
        (fun j (a : CoordinateRealTwoForm n) => a ![v (σ (q (j, 0))), v (σ (q (j, 1)))])
        A i c j
  rw [hprod, hprod, hprod]
  have hxy : (x + y) ![v (σ (q (i, 0))), v (σ (q (i, 1)))] =
      x ![v (σ (q (i, 0))), v (σ (q (i, 1)))] + y ![v (σ (q (i, 0))), v (σ (q (i, 1)))] := rfl
  rw [hxy]
  ring

theorem coordinatePairingSumFamily_update_smul (A : Fin k → CoordinateRealTwoForm n)
    (i : Fin k) (r : ℝ) (x : CoordinateRealTwoForm n) (q : Fin k × Fin 2 → ι)
    (v : ι → ComplexModel n) :
    coordinatePairingSumFamily (Function.update A i (r • x)) q v =
      r * coordinatePairingSumFamily (Function.update A i x) q v := by
  unfold coordinatePairingSumFamily
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hprod : ∀ c : CoordinateRealTwoForm n,
      ∏ j : Fin k, (Function.update A i c) j ![v (σ (q (j, 0))), v (σ (q (j, 1)))] =
        c ![v (σ (q (i, 0))), v (σ (q (i, 1)))] *
          ∏ j ∈ Finset.univ \ {i}, A j ![v (σ (q (j, 0))), v (σ (q (j, 1)))] := by
    intro c
    rw [← Finset.prod_update_of_mem (Finset.mem_univ i)
      (fun j : Fin k => A j ![v (σ (q (j, 0))), v (σ (q (j, 1)))])
      (c ![v (σ (q (i, 0))), v (σ (q (i, 1)))])]
    exact Finset.prod_congr rfl fun j _ =>
      Function.apply_update
        (fun j (a : CoordinateRealTwoForm n) => a ![v (σ (q (j, 0))), v (σ (q (j, 1)))])
        A i c j
  rw [hprod, hprod]
  have hrx : (r • x) ![v (σ (q (i, 0))), v (σ (q (i, 1)))] =
      r * x ![v (σ (q (i, 0))), v (σ (q (i, 1)))] := rfl
  rw [hrx]
  ring

end Multilinear

/-! ## Symmetry under permuting the slots

Permuting the slots by `τ` reindexes the product by `τ⁻¹`, which precomposes the pairing
map `q` with the block permutation `(i, b) ↦ (τ⁻¹ i, b)` of `Fin k × Fin 2`.  The sum over
`Equiv.Perm ι` absorbs that precomposition at the cost of the sign of the block
permutation, and that sign is `(sign τ⁻¹)² = 1` because each of the `2` layers contributes
one copy of `τ⁻¹`.  This is the precise sense in which two-forms commute. -/

section Symmetry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- Precomposing the pairing map with a permutation of `Fin k × Fin 2` multiplies the
pairing sum by the sign of that permutation. -/
theorem coordinatePairingSumFamily_precomp_perm (A : Fin k → CoordinateRealTwoForm n)
    (q : Fin k × Fin 2 ≃ ι) (ρ : Equiv.Perm (Fin k × Fin 2)) (v : ι → ComplexModel n) :
    coordinatePairingSumFamily A (⇑q ∘ ⇑ρ) v =
      ((Equiv.Perm.sign ρ : ℤ) : ℝ) * coordinatePairingSumFamily A (⇑q) v := by
  classical
  set π : Equiv.Perm ι := q.permCongr ρ with hπ
  have hqρ : ∀ z : Fin k × Fin 2, q (ρ z) = π (q z) := by
    intro z
    simp [hπ, Equiv.permCongr_apply]
  set T : Equiv.Perm ι → ℝ := fun ν =>
    ∏ i : Fin k, A i ![v (ν (q (i, 0))), v (ν (q (i, 1)))] with hT
  have hL : coordinatePairingSumFamily A (⇑q ∘ ⇑ρ) v =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * T (σ * π) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, hqρ, Equiv.Perm.mul_apply]
  have hsq : ((Equiv.Perm.sign π : ℤ) : ℝ) * ((Equiv.Perm.sign π : ℤ) : ℝ) = 1 := by
    have : ((Equiv.Perm.sign π : ℤ) * (Equiv.Perm.sign π : ℤ)) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
    exact_mod_cast this
  have hsign : ∀ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * T (σ * π) =
      ((Equiv.Perm.sign π : ℤ) : ℝ) *
        (((Equiv.Perm.sign (σ * π) : ℤ) : ℝ) * T (σ * π)) := by
    intro σ
    have h1 : ((Equiv.Perm.sign (σ * π) : ℤ) : ℝ) =
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign π : ℤ) : ℝ) := by
      rw [Equiv.Perm.sign_mul]
      push_cast
      ring
    rw [h1]
    have h2 : ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ((((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign π : ℤ) : ℝ)) * T (σ * π)) =
          (((Equiv.Perm.sign π : ℤ) : ℝ) * ((Equiv.Perm.sign π : ℤ) : ℝ)) *
            (((Equiv.Perm.sign σ : ℤ) : ℝ) * T (σ * π)) := by ring
    rw [h2, hsq, one_mul]
  have hsum : (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign (σ * π) : ℤ) : ℝ) * T (σ * π)) =
      coordinatePairingSumFamily A (⇑q) v :=
    Equiv.sum_comp (Equiv.mulRight π)
      (fun ν : Equiv.Perm ι => ((Equiv.Perm.sign ν : ℤ) : ℝ) * T ν)
  rw [hL]
  simp only [hsign, ← Finset.mul_sum]
  rw [hsum, hπ, Equiv.Perm.sign_permCongr]

/-- **The pairing sum is symmetric in the slots.**  This is "two-forms commute" in the
Pfaffian representation. -/
theorem coordinatePairingSumFamily_comp_perm (A : Fin k → CoordinateRealTwoForm n)
    (q : Fin k × Fin 2 ≃ ι) (τ : Equiv.Perm (Fin k)) (v : ι → ComplexModel n) :
    coordinatePairingSumFamily (fun i => A (τ i)) (⇑q) v =
      coordinatePairingSumFamily A (⇑q) v := by
  classical
  set ρ : Equiv.Perm (Fin k × Fin 2) :=
    Equiv.prodCongrLeft (fun _ : Fin 2 => (τ⁻¹ : Equiv.Perm (Fin k))) with hρ
  have hρapp : ∀ (j : Fin k) (b : Fin 2), ρ (j, b) = (τ⁻¹ j, b) := by
    intro j b
    rw [hρ]
    rfl
  have hstep : coordinatePairingSumFamily (fun i => A (τ i)) (⇑q) v =
      coordinatePairingSumFamily A (⇑q ∘ ⇑ρ) v := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    calc ∏ i : Fin k, A (τ i) ![v (σ (q (i, 0))), v (σ (q (i, 1)))]
        = ∏ i : Fin k, (fun j : Fin k =>
            A j ![v (σ (q (τ⁻¹ j, 0))), v (σ (q (τ⁻¹ j, 1)))]) (τ i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp
      _ = ∏ j : Fin k, A j ![v (σ (q (τ⁻¹ j, 0))), v (σ (q (τ⁻¹ j, 1)))] :=
          Equiv.prod_comp τ (fun j : Fin k =>
            A j ![v (σ (q (τ⁻¹ j, 0))), v (σ (q (τ⁻¹ j, 1)))])
      _ = ∏ i : Fin k, A i ![v (σ ((⇑q ∘ ⇑ρ) (i, 0))), v (σ ((⇑q ∘ ⇑ρ) (i, 1)))] := by
          refine Finset.prod_congr rfl fun j _ => ?_
          simp only [Function.comp_apply, hρapp]
  have hsign : Equiv.Perm.sign ρ = 1 := by
    rw [hρ, Equiv.Perm.sign_prodCongrLeft]
    simp [Int.units_sq]
  rw [hstep, coordinatePairingSumFamily_precomp_perm, hsign]
  norm_num

end Symmetry

/-! ## The mixed top density is symmetric and multilinear

These are the two properties of `actualMixedTopDensity` that the recursive definition does
not show and that polarization against the pure identity needs. -/

theorem actualMixedTopDensity_eq_pairingSum (A : Fin n → CoordinateRealTwoForm n) :
    actualMixedTopDensity A = ((2 : ℝ) ^ n)⁻¹ *
      coordinatePairingSumFamily A (finProdFinEquiv : Fin n × Fin 2 → Fin (n * 2))
        coordinateRealFrame :=
  coordinateWedgeFamily_apply_eq_pairingSum n A coordinateRealFrame

/-- The mixed top density as an `ℝ`-multilinear function of the `n` two-forms. -/
def actualMixedTopDensityMultilinear :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => CoordinateRealTwoForm n) ℝ where
  toFun := actualMixedTopDensity
  map_update_add' := by
    intro _ A i x y
    simp only [actualMixedTopDensity_eq_pairingSum, coordinatePairingSumFamily_update_add]
    ring
  map_update_smul' := by
    intro _ A i c x
    simp only [actualMixedTopDensity_eq_pairingSum, coordinatePairingSumFamily_update_smul,
      RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem actualMixedTopDensityMultilinear_apply (A : Fin n → CoordinateRealTwoForm n) :
    actualMixedTopDensityMultilinear A = actualMixedTopDensity A := rfl

/-- **The mixed exterior product is symmetric in its factors.** -/
theorem actualMixedTopDensity_perm (A : Fin n → CoordinateRealTwoForm n)
    (τ : Equiv.Perm (Fin n)) :
    actualMixedTopDensity (fun i => A (τ i)) = actualMixedTopDensity A := by
  rw [actualMixedTopDensity_eq_pairingSum, actualMixedTopDensity_eq_pairingSum,
    coordinatePairingSumFamily_comp_perm A finProdFinEquiv τ]

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
