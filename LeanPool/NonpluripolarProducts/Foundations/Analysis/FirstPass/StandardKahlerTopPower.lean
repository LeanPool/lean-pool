/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateWedgePullback

/-!
# The top power of the standard Kähler form

Let `A` be a real two-form on `ComplexModel n` with `A(v, w) = Im ⟪v, w⟫_ℂ`,
i.e. the standard Kähler form `∑ⱼ dxⱼ ∧ dyⱼ`.  We prove that its genuine
top exterior power evaluates on the standard real frame
`e₀, I e₀, e₁, I e₁, ...` to `n!`; in particular it is positive.

The proof goes through a Pfaffian-type formula for exterior powers of an
arbitrary two-form:
`A^{∧k}(v) = 2⁻ᵏ ∑_{σ} sign σ ∏_{i < k} A(v_{σ(2i)}, v_{σ(2i+1)})`,
proved by induction from the shuffle formula for `coordinateWedgeSum`.
For the standard form on the standard frame, the nonzero terms are exactly
the permutations preserving the block decomposition into the pairs
`{2j, 2j+1}`; each contributes `1`, and there are `n! 2ⁿ` of them.
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

theorem coordinateWedge_apply_eq_pairingSum (A : CoordinateRealTwoForm n) {j : ℕ}
    (P : (ComplexModel n) [⋀^Fin (j * 2)]→L[ℝ] ℝ)
    (hP : ∀ u, P u = ((2 : ℝ) ^ j)⁻¹ *
      coordinatePairingSum A (finProdFinEquiv : Fin j × Fin 2 → Fin (j * 2)) u)
    (v : Fin ((j + 1) * 2) → ComplexModel n) :
    coordinateWedge P A (v ∘ Fin.cast (show j * 2 + 2 = (j + 1) * 2 by ring)) =
      ((2 : ℝ) ^ (j + 1))⁻¹ *
        coordinatePairingSum A (finProdFinEquiv : Fin (j + 1) × Fin 2 → Fin ((j + 1) * 2)) v := by
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
  rw [hfp, coordinatePairingSum_equiv, coordinateWedge_apply, coordinateWedgeSum_apply]
  have hwe : (v ∘ Fin.cast h) ∘ finSumFinEquiv = v ∘ e := rfl
  rw [hwe]
  set w : Fin (j * 2) ⊕ Fin 2 → ComplexModel n := v ∘ e with hw
  clear_value w q
  set F : Equiv.Perm (Fin (j * 2) ⊕ Fin 2) → ℝ := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∏ i : Fin (j + 1), A ![w (σ (q (i, 0))), w (σ (q (i, 1)))] with hF
  have key : ∀ τ : Equiv.Perm (Fin (j * 2) ⊕ Fin 2),
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * (P (w ∘ ⇑τ ∘ Sum.inl) * A (w ∘ ⇑τ ∘ Sum.inr)) =
        ((2 : ℝ) ^ j)⁻¹ * ∑ ρ : Equiv.Perm (Fin (j * 2)), F (τ * Equiv.Perm.sumCongr ρ 1) := by
    intro τ
    rw [hP, coordinatePairingSum, twoForm_apply_eq A]
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
  have hS : coordinatePairingSum A q w = ∑ x, F x := rfl
  rw [hS, Nat.factorial_two, pow_succ]
  have : ((j * 2).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Pfaffian-type formula for the exterior powers of a real two-form. -/
theorem coordinateWedgePower_apply_eq_pairingSum (A : CoordinateRealTwoForm n) (k : ℕ)
    (v : Fin (k * 2) → ComplexModel n) :
    coordinateWedgePower A k v = ((2 : ℝ) ^ k)⁻¹ *
      coordinatePairingSum A (finProdFinEquiv : Fin k × Fin 2 → Fin (k * 2)) v := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
      simp [coordinatePairingSum, coordinateWedgePower, coordinateWedgeUnit]
    | 1, _ =>
      have hterm : ∀ σ : Equiv.Perm (Fin (1 * 2)), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i : Fin 1, A ![v (σ (finProdFinEquiv (i, 0))), v (σ (finProdFinEquiv (i, 1)))] =
            A v := by
        intro σ
        rw [Fin.prod_univ_one]
        have hv : A ![v (σ (finProdFinEquiv ((0 : Fin 1), (0 : Fin 2)))),
            v (σ (finProdFinEquiv ((0 : Fin 1), (1 : Fin 2))))] = A (v ∘ σ) := by
          rw [twoForm_apply_eq A (v ∘ σ)]
          rfl
        rw [hv, ← A.coe_toAlternatingMap, AlternatingMap.map_perm, Units.smul_def,
          zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
        simp
      simp only [coordinatePairingSum, hterm, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      change A v = _
      ring
    | k + 2, ih =>
      rw [coordinateWedgePower_add_two_apply]
      exact coordinateWedge_apply_eq_pairingSum A _ (ih (k + 1) (by omega)) v

theorem coordinateRealFrame_finProdFinEquiv (j : Fin n) (b : Fin 2) :
    coordinateRealFrame (finProdFinEquiv (j, b)) =
      if b = 0 then coordinateVector j else Complex.I • coordinateVector j := by
  simp [coordinateRealFrame]

/-- The values of the standard Kähler form on pairs of standard frame vectors. -/
theorem apply_coordinateRealFrame_of_apply_eq_im (A : CoordinateRealTwoForm n)
    (hA : ∀ v w : ComplexModel n, A ![v, w] = (inner ℂ v w).im) (a c : Fin n × Fin 2) :
    A ![coordinateRealFrame (finProdFinEquiv a), coordinateRealFrame (finProdFinEquiv c)] =
      if a.1 = c.1 then ((c.2 : ℕ) : ℝ) - ((a.2 : ℕ) : ℝ) else 0 := by
  obtain ⟨j, b⟩ := a
  obtain ⟨j', b'⟩ := c
  rw [hA, coordinateRealFrame_finProdFinEquiv, coordinateRealFrame_finProdFinEquiv]
  fin_cases b <;> fin_cases b' <;>
    by_cases hj : j = j' <;>
    simp [hj, coordinateVector, EuclideanSpace.inner_single_left, inner_smul_left,
      inner_smul_right, -inner_self_eq_norm_sq_to_K]

private theorem sign_fin_two_eq (τ : Equiv.Perm (Fin 2)) :
    ((τ 1 : ℕ) : ℝ) - ((τ 0 : ℕ) : ℝ) = ((Equiv.Perm.sign τ : ℤ) : ℝ) := by
  have h : ∀ τ : Equiv.Perm (Fin 2), ((τ 1 : ℕ) : ℤ) - ((τ 0 : ℕ) : ℤ) =
      (Equiv.Perm.sign τ : ℤ) := by decide
  rw [← h τ]
  push_cast
  ring

/-- The block permutation `(i, b) ↦ (π i, ε i b)` has sign `∏ᵢ sign (ε i)`. -/
private theorem sign_prodShear {k : ℕ} (π : Equiv.Perm (Fin k))
    (ε : Fin k → Equiv.Perm (Fin 2)) :
    Equiv.Perm.sign (Equiv.prodShear π ε) = ∏ i, Equiv.Perm.sign (ε i) := by
  have h : (Equiv.prodShear π ε : Equiv.Perm (Fin k × Fin 2)) =
      Equiv.prodCongrLeft (fun _ : Fin 2 => π) * Equiv.prodCongrRight ε := by
    ext x <;> rfl
  rw [h, Equiv.Perm.sign_mul, Equiv.Perm.sign_prodCongrLeft, Equiv.Perm.sign_prodCongrRight,
    Fin.prod_univ_two, Int.units_mul_self, one_mul]

/-- The Pfaffian-type sum of the standard Kähler form on the standard frame. -/
theorem coordinatePairingSum_frame_of_apply_eq_im (A : CoordinateRealTwoForm n)
    (hA : ∀ v w : ComplexModel n, A ![v, w] = (inner ℂ v w).im) :
    coordinatePairingSum A (id : Fin n × Fin 2 → Fin n × Fin 2)
        (coordinateRealFrame ∘ finProdFinEquiv) =
      (n.factorial : ℝ) * 2 ^ n := by
  have hM := apply_coordinateRealFrame_of_apply_eq_im A hA
  unfold coordinatePairingSum
  simp only [id, Function.comp_apply, hM]
  set Φ : Equiv.Perm (Fin n) × (Fin n → Equiv.Perm (Fin 2)) → Equiv.Perm (Fin n × Fin 2) :=
    fun x => Equiv.prodShear x.1 x.2 with hΦ
  have hΦinj : Function.Injective Φ := by
    rintro ⟨π, ε⟩ ⟨π', ε'⟩ hx
    have hx' : ∀ i b, (π i, ε i b) = (π' i, ε' i b) := fun i b =>
      congrArg (fun σ : Equiv.Perm (Fin n × Fin 2) => σ (i, b)) hx
    refine Prod.ext (Equiv.ext fun i => congrArg Prod.fst (hx' i 0)) ?_
    funext i
    exact Equiv.ext fun b => congrArg Prod.snd (hx' i b)
  refine ((Finset.sum_of_injOn Φ hΦinj.injOn
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ (s := Finset.univ)
    (f := fun _ => (1 : ℝ)) ?_).symm).trans ?_
  · intro σ _ hσ
    by_contra hne
    apply hσ
    have hprod := right_ne_zero_of_mul hne
    rw [Finset.prod_ne_zero_iff] at hprod
    have hfst : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1 := by
      intro i
      by_contra hi
      exact hprod i (Finset.mem_univ _) (ite_eq_right hi)
    have hfst' : ∀ i b, (σ (i, b)).1 = (σ (i, 0)).1 := by
      intro i b
      fin_cases b
      · rfl
      · exact (hfst i).symm
    have hπ : Function.Injective fun i => (σ (i, 0)).1 := by
      intro i i' hii'
      simp only at hii'
      have hab : σ (i, 0) ≠ σ (i, 1) := fun h => by
        simpa using σ.injective h
      have hab2 : (σ (i, 0)).2 ≠ (σ (i, 1)).2 := fun h => hab (Prod.ext (hfst i) h)
      have hc : (σ (i', 0)).2 = (σ (i, 0)).2 ∨ (σ (i', 0)).2 = (σ (i, 1)).2 := by
        have h1 := (σ (i', 0)).2.isLt
        have h2 := (σ (i, 0)).2.isLt
        have h3 := (σ (i, 1)).2.isLt
        have h4 : ((σ (i, 0)).2 : ℕ) ≠ (σ (i, 1)).2 := fun h => hab2 (Fin.ext h)
        rcases Nat.lt_or_ge ((σ (i', 0)).2 : ℕ) 1 with h5 | h5
        · rcases Nat.lt_or_ge ((σ (i, 0)).2 : ℕ) 1 with h6 | h6
          · left; exact Fin.ext (by omega)
          · right; exact Fin.ext (by omega)
        · rcases Nat.lt_or_ge ((σ (i, 0)).2 : ℕ) 1 with h6 | h6
          · right; exact Fin.ext (by omega)
          · left; exact Fin.ext (by omega)
      rcases hc with hc | hc
      · have := σ.injective (Prod.ext hii' hc.symm)
        exact congrArg Prod.fst this
      · have := σ.injective (Prod.ext ((hfst i).symm.trans hii') hc.symm)
        simp at this
    have hε : ∀ i, Function.Injective fun b => (σ (i, b)).2 := by
      intro i b b' hbb'
      have := σ.injective (Prod.ext ((hfst' i b).trans (hfst' i b').symm) hbb')
      simpa using this
    refine ⟨(Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hπ),
      fun i => Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (hε i))),
      Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    ext x
    · obtain ⟨i, b⟩ := x
      simp [hΦ, Equiv.prodShear, hfst' i b]
    · obtain ⟨i, b⟩ := x
      simp [hΦ, Equiv.prodShear]
  · rintro ⟨π, ε⟩ _
    simp only [hΦ, Equiv.prodShear_apply, ite_true, sign_fin_two_eq, sign_prodShear,
      Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
    symm
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  · simp [Fintype.card_perm, Fintype.card_pi]

/-- The top exterior power of the standard Kähler form `Im ⟪v, w⟫_ℂ` has
density `n!` in the standard complex orientation. -/
theorem actualTopPowerDensity_eq_factorial_of_apply_eq_im {n : ℕ} (A : CoordinateRealTwoForm n)
    (hA : ∀ v w : ComplexModel n, A ![v, w] = (inner ℂ v w).im) :
    actualTopPowerDensity A = n.factorial := by
  have h := coordinatePairingSum_equiv A (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2)) id
    coordinateRealFrame
  rw [Function.comp_id] at h
  rw [actualTopPowerDensity, coordinateWedgePower_apply_eq_pairingSum, h,
    coordinatePairingSum_frame_of_apply_eq_im A hA]
  field_simp

/-- The top exterior power of the standard Kähler form has positive density. -/
theorem actualTopPowerDensity_pos_of_apply_eq_im {n : ℕ} (A : CoordinateRealTwoForm n)
    (hA : ∀ v w : ComplexModel n, A ![v, w] = (inner ℂ v w).im) :
    0 < actualTopPowerDensity A := by
  rw [actualTopPowerDensity_eq_factorial_of_apply_eq_im A hA]
  exact_mod_cast n.factorial_pos

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
