/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardKahlerTopPower

/-!
# A weighted diagonal Pfaffian computation

This is the purely finite-combinatorial diagonal case of the real-frame
Pfaffian-to-determinant comparison.  If a two-form has independent standard
real `2 × 2` blocks with weights `d j`, its pairing sum on the interleaved
real frame is `n! 2^n ∏ j, d j`.

The proof does not assume a Pfaffian--determinant identity.  It classifies
nonzero summands directly as block permutations, then proves that the sign of
each within-block permutation cancels its oriented block coefficient.
-/

@[expose] public section

noncomputable section

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

private theorem weightedDiagonal_sign_fin_two_eq (τ : Equiv.Perm (Fin 2)) :
    ((τ 1 : ℕ) : ℝ) - ((τ 0 : ℕ) : ℝ) = ((Equiv.Perm.sign τ : ℤ) : ℝ) := by
  have h : ∀ τ : Equiv.Perm (Fin 2), ((τ 1 : ℕ) : ℤ) - ((τ 0 : ℕ) : ℤ) =
      (Equiv.Perm.sign τ : ℤ) := by decide
  rw [← h τ]
  push_cast
  ring

/-- The sign of an interleaved block permutation is the product of its
within-block signs. -/
private theorem weightedDiagonal_sign_prodShear {k : ℕ} (π : Equiv.Perm (Fin k))
    (ε : Fin k → Equiv.Perm (Fin 2)) :
    Equiv.Perm.sign (Equiv.prodShear π ε) = ∏ i, Equiv.Perm.sign (ε i) := by
  have h : (Equiv.prodShear π ε : Equiv.Perm (Fin k × Fin 2)) =
      Equiv.prodCongrLeft (fun _ : Fin 2 => π) * Equiv.prodCongrRight ε := by
    ext x <;> rfl
  rw [h, Equiv.Perm.sign_mul, Equiv.Perm.sign_prodCongrLeft,
    Equiv.Perm.sign_prodCongrRight, Fin.prod_univ_two, Int.units_mul_self, one_mul]

/-- For a block permutation, the orientation of every `2 × 2` block cancels
its permutation sign, while the outer block permutation merely reindexes the
weights. -/
private theorem weightedDiagonal_prodShear_term (π : Equiv.Perm (Fin n))
    (ε : Fin n → Equiv.Perm (Fin 2)) (d : Fin n → ℝ) :
    ((Equiv.Perm.sign (Equiv.prodShear π ε) : ℤ) : ℝ) *
        ∏ i : Fin n, d (π i) *
          ((((ε i) 1 : ℕ) : ℝ) - (((ε i) 0 : ℕ) : ℝ)) =
      ∏ i : Fin n, d i := by
  rw [weightedDiagonal_sign_prodShear, Units.coe_prod, Int.cast_prod,
    ← Finset.prod_mul_distrib]
  calc
    (∏ i : Fin n, ((Equiv.Perm.sign (ε i) : ℤ) : ℝ) *
        (d (π i) * ((((ε i) 1 : ℕ) : ℝ) - (((ε i) 0 : ℕ) : ℝ)))) =
        (∏ i : Fin n, d (π i)) * ∏ i : Fin n,
          ((Equiv.Perm.sign (ε i) : ℤ) : ℝ) *
            ((((ε i) 1 : ℕ) : ℝ) - (((ε i) 0 : ℕ) : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = ∏ i : Fin n, d (π i) := by
      have hone : ∏ i : Fin n, ((Equiv.Perm.sign (ε i) : ℤ) : ℝ) *
          ((((ε i) 1 : ℕ) : ℝ) - (((ε i) 0 : ℕ) : ℝ)) = 1 := by
        apply Finset.prod_eq_one
        intro i _
        rw [weightedDiagonal_sign_fin_two_eq, ← Int.cast_mul, ← Units.val_mul,
          Int.units_mul_self]
        simp
      rw [hone, mul_one]
    _ = ∏ i : Fin n, d i := Equiv.prod_comp π d

/-- The pairing sum of a diagonal collection of real `2 × 2` blocks.  The
hypothesis is a coefficient-level statement, so this result can be used after
any analytic argument which identifies a form with such a diagonal frame. -/
theorem coordinatePairingSum_frame_of_diagonal_weights (A : CoordinateRealTwoForm n)
    (d : Fin n → ℝ)
    (hA : ∀ a c : Fin n × Fin 2,
      A ![coordinateRealFrame (finProdFinEquiv a), coordinateRealFrame (finProdFinEquiv c)] =
        if a.1 = c.1 then d a.1 * (((c.2 : ℕ) : ℝ) - ((a.2 : ℕ) : ℝ)) else 0) :
    coordinatePairingSum A (id : Fin n × Fin 2 → Fin n × Fin 2)
        (coordinateRealFrame ∘ finProdFinEquiv) =
      (n.factorial : ℝ) * 2 ^ n * ∏ j, d j := by
  unfold coordinatePairingSum
  simp only [id, Function.comp_apply, hA]
  set Φ : Equiv.Perm (Fin n) × (Fin n → Equiv.Perm (Fin 2)) →
      Equiv.Perm (Fin n × Fin 2) := fun x => Equiv.prodShear x.1 x.2 with hΦ
  have hΦinj : Function.Injective Φ := by
    rintro ⟨π, ε⟩ ⟨π', ε'⟩ hx
    have hx' : ∀ i b, (π i, ε i b) = (π' i, ε' i b) := fun i b =>
      congrArg (fun σ : Equiv.Perm (Fin n × Fin 2) => σ (i, b)) hx
    refine Prod.ext (Equiv.ext fun i => congrArg Prod.fst (hx' i 0)) ?_
    funext i
    exact Equiv.ext fun b => congrArg Prod.snd (hx' i b)
  refine ((Finset.sum_of_injOn Φ hΦinj.injOn
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ (s := Finset.univ)
    (f := fun _ => ∏ j : Fin n, d j) ?_).symm).trans ?_
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
    simpa only [hΦ, Equiv.prodShear_apply, ite_true] using
      (weightedDiagonal_prodShear_term π ε d).symm
  · simp [Fintype.card_perm, Fintype.card_pi, nsmul_eq_mul]

/-- The corresponding genuine exterior-power density.  This is the analytic
interface of the combinatorial computation: diagonal real-frame coefficients
can be inserted directly into `actualTopPowerDensity`. -/
theorem actualTopPowerDensity_eq_factorial_mul_prod_of_diagonal_weights
    (A : CoordinateRealTwoForm n) (d : Fin n → ℝ)
    (hA : ∀ a c : Fin n × Fin 2,
      A ![coordinateRealFrame (finProdFinEquiv a), coordinateRealFrame (finProdFinEquiv c)] =
        if a.1 = c.1 then d a.1 * (((c.2 : ℕ) : ℝ) - ((a.2 : ℕ) : ℝ)) else 0) :
    actualTopPowerDensity A = (n.factorial : ℝ) * ∏ j, d j := by
  have h := coordinatePairingSum_equiv A
    (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2)) id coordinateRealFrame
  rw [Function.comp_id] at h
  rw [actualTopPowerDensity, coordinateWedgePower_apply_eq_pairingSum, h,
    coordinatePairingSum_frame_of_diagonal_weights A d hA]
  field_simp

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
