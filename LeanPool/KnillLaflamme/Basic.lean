/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import LeanPool.KnillLaflamme.QuantumInfo.KnillLaflamme

/-!
# The Knill–Laflamme theorem, in two forms

`QuantumInfo.knillLaflamme_iff` (in `LeanPool.KnillLaflamme.QuantumInfo.KnillLaflamme`) states the
equivalence with the recovery's Kraus operators indexed by `Option ι`, the errors plus one. This
file proves the two statements of `Challenge.lean`.

* `knill_laflamme`: the condition holds if and only if some channel, with any finite number of
  Kraus operators, corrects **each** error up to its own scalar. The forward direction relabels
  the `Option ι` recovery along `Option ι ≃ Fin (card (Option ι))`, which changes neither its
  trace preservation nor its action; the converse is `knillLaflamme_of_recovery`.
* `knill_laflamme_sum`: the condition holds if and only if some channel corrects the **combined**
  noise `ρ ↦ ∑ᵢ Eᵢ ρ Eᵢᴴ` up to a scalar. The errors need not form a channel: the noise may lose
  trace. Its converse is `knillLaflamme_of_recovery_sum`.

The two recovery conditions are equivalent even for the same channel `R`. If `R` corrects each
error, it corrects the sum by linearity. If `R` corrects the sum, the proof of
`knillLaflamme_of_recovery_sum` shows that each `R k Eᵢ P` is a scalar multiple of `P`, so `R`
corrects each error.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

namespace Channel

variable {n m ι κ : Type*} [Fintype n] [Fintype m] [Fintype ι] [Fintype κ] [DecidableEq n]

/-- The channel with the same Kraus operators, relabelled along an equivalence `e : ι ≃ κ`. -/
def reindex (e : ι ≃ κ) (Φ : Channel n m ι) : Channel n m κ where
  kraus k := Φ.kraus (e.symm k)
  tp := (Equiv.sum_comp e.symm fun i => (Φ.kraus i)ᴴ * Φ.kraus i).trans Φ.tp

/-- Relabelling the Kraus operators does not change the channel's action. -/
theorem reindex_apply (e : ι ≃ κ) (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    (Φ.reindex e).apply ρ = Φ.apply ρ :=
  Equiv.sum_comp e.symm fun i => Φ.kraus i * ρ * (Φ.kraus i)ᴴ

end Channel

variable {n : Type*} [Fintype n]

variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The converse for the combined noise.** If a channel `R` corrects the combined noise
`ρ ↦ ∑ᵢ Eᵢ ρ Eᵢᴴ` on the code `P` up to a scalar, the errors satisfy the Knill–Laflamme condition.
Every pair `(k, i)` gives the operator `R k Eᵢ P`, and together they satisfy the hypothesis of
`exists_smul_of_sum_conj_eq`, so each is a scalar multiple of `P`; trace preservation then gives
the condition, as in `knillLaflamme_of_recovery`. -/
theorem knillLaflamme_of_recovery_sum {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ}
    (hP : IsCodeProjector P) {κ : Type*} [Fintype κ] (R : Channel n n κ) (lam : ℂ)
    (h : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (∑ i, E i * ρ * (E i)ᴴ) = lam • ρ) :
    ∃ c : Matrix ι ι ℂ, KnillLaflamme P E c := by
  have hscal : ∀ i k, ∃ μ : ℂ, R.kraus k * E i * P = μ • P := by
    intro i k
    refine exists_smul_of_sum_conj_eq hP (fun p : κ × ι => R.kraus p.1 * E p.2 * P) lam
      (fun p => by rw [Matrix.mul_assoc, hP.mul_self]) (fun X => ?_) (k, i)
    have hX : P * X * P = P * (P * X * P) * P := by
      conv_rhs => rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.mul_self,
        Matrix.mul_assoc (P * X), hP.mul_self]
    rw [← h (P * X * P) hX, Channel.apply_def, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq]
    simp only [Matrix.mul_assoc]
  choose μ hμ using hscal
  exact ⟨_, knillLaflamme_of_kraus_scalars hP R μ hμ⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **The Knill–Laflamme theorem.** On a nonzero code `P`, the errors `E` satisfy the
Knill–Laflamme condition for some matrix `c` if and only if they are correctable: some channel
`R`, with any finite number of Kraus operators, undoes each error on every code state up to a
scalar. -/
theorem knill_laflamme [Finite ι] {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} (hP : IsCodeProjector P)
    (hP0 : P ≠ 0) :
    (∃ c : Matrix ι ι ℂ, KnillLaflamme P E c) ↔
      ∃ (m : ℕ) (R : Channel n n (Fin m)) (lam : ι → ℂ),
        ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro h
    obtain ⟨R, lam, hR⟩ := (knillLaflamme_iff hP hP0).mp h
    refine ⟨_, R.reindex (Fintype.equivFin (Option ι)), lam, fun i ρ hρ => ?_⟩
    rw [Channel.reindex_apply]
    exact hR i ρ hρ
  · rintro ⟨m, R, lam, h⟩
    exact knillLaflamme_of_recovery hP R lam h

omit [DecidableEq ι] in
/-- **The Knill–Laflamme theorem for the combined noise.** On a nonzero code `P`, the errors `E`
satisfy the Knill–Laflamme condition for some matrix `c` if and only if some channel `R`, with any
finite number of Kraus operators, undoes the combined noise `ρ ↦ ∑ᵢ Eᵢ ρ Eᵢᴴ` on every code state
up to a scalar. The errors need not form a channel. -/
theorem knill_laflamme_sum {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} (hP : IsCodeProjector P)
    (hP0 : P ≠ 0) :
    (∃ c : Matrix ι ι ℂ, KnillLaflamme P E c) ↔
      ∃ (m : ℕ) (R : Channel n n (Fin m)) (lam : ℂ),
        ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (∑ i, E i * ρ * (E i)ᴴ) = lam • ρ := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme hP hP0 hc
    refine ⟨_, R.reindex (Fintype.equivFin (Option ι)), ∑ i, c i i, fun ρ hρ => ?_⟩
    rw [Channel.reindex_apply, Channel.apply_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => hR ρ hρ i i
  · rintro ⟨m, R, lam, h⟩
    exact knillLaflamme_of_recovery_sum hP R lam h

end QuantumInfo
