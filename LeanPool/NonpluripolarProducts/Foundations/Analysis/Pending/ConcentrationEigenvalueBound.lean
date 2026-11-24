/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoefficientCongruence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoefficientPositivity
public import Mathlib.Analysis.Matrix.PosDef

/-!
# The pointwise eigenvalue estimate of Demailly--Păun's concentration of mass

Source: Demailly--Păun, *Numerical characterization of the Kähler cone*, proof of Proposition 2.6
(`dp04-kahler-cone:2.6`, `references/dp04-kahler-cone/source/0105176.tex:835-900`, inequalities
(2.7'), (2.9'), (2.9'')), used verbatim in Boucksom's proof of the bigness criterion
(`bou02-volume:4.12`, items (a)-(c); `bou02-volume:4.8`).  Phase TN.4, plan
the proof of Boucksom's mass estimate, item #1, step B3.

At a point, with `λ₁ ≤ … ≤ λₙ` the eigenvalues of `α_ε` relative to `ω_ε`, the source uses
`α_ε^p ≥ λ₁⋯λ_p ω_ε^p` (2.9') and `α_ε^{n-p} ∧ ω_ε^p ≥ (1/n!) λ_{p+1}⋯λₙ ω_ε^n` (2.9'') off and on
the set where the product of the `n - p` largest eigenvalues is large.  Here everything is a top
degree mixed product, i.e. a value of the project's mixed coefficient
`FirstPass.MixedMongeAmpere.mixedCoefficient` (the coefficient of `t₁⋯tₙ` in `det(∑ tᵢ Hᵢ)`),
    and the
estimate is stated WITHOUT eigenvalues: the set "`λ_{p+1}⋯λₙ` large" is replaced by the set where
the mixed coefficient `C(A[n-p], B[p])` is large compared with `det B` -- a continuous function of
the point, so the source's integration step (Markov on that set) applies directly.

## Main results

* `concentration_bound` — for `A, B ≻ 0`, `C ≥ 0`, `p ≤ n`, `t > 0`: if
  `Re C(A[n-p], B[p]) < t · Re det B` then
  `Re det A / (t · Re det B) · Re C(B[p], C[n-p]) ≤ Re C(A[p], C[n-p])`.
* `diagonal_concentration_bound` — the same with `A = diag(λ)`, `B = 1`.
* `exists_simultaneous_diagonalization` — `R^* B R = 1`, `R^* A R = diag(λ)`, `λ > 0`.
* `mixedCoefficient_unitDiag` (`C(E_{j 0}, …) = [j bijective]`), `mixedCoefficient_ite_diagonal`
  (expansion of diagonal slots), `mixedCoefficient_diagonal_family` (permanent formula),
  `le_re_mixedCoefficient_ite_diagonal`, `prod_le_re_mixedCoefficient_ite_diagonal'`.

No consumer yet: the concentration argument (B3) is assembled once the diagonal mass concentration
(`dp04-kahler-cone:2.1`) and the currents of bidegree `(p, p)` (B2) are in place.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.ConcentrationEigenvalueBound

open FirstPass.MixedMongeAmpere Pending.MixedMongeAmpere

variable {n : ℕ}

/-- The diagonal unit matrix `E_k = diag(e_k)`. -/
noncomputable def unitDiag (k : Fin n) : Matrix (Fin n) (Fin n) ℂ := diagonal (Pi.single k 1)

theorem unitDiag_posSemidef (k : Fin n) : (unitDiag k).PosSemidef := by
  unfold unitDiag
  refine PosSemidef.diagonal ?_
  intro i
  by_cases h : i = k
  · subst h; simp
  · simp [h]

/-- **Mixed coefficient of diagonal unit matrices**: `C(E_{j 0}, …, E_{j (n-1)})` is `1` if `j` is
    a
bijection and `0` otherwise. -/
theorem mixedCoefficient_unitDiag (j : Fin n → Fin n) :
    mixedCoefficient (fun i => unitDiag (j i)) = if Function.Bijective j then 1 else 0 := by
  classical
  have hterm (σ : Equiv.Perm (Fin n)) :
      Matrix.det (fun r k => unitDiag (j (σ r)) r k) = if ∀ r, j (σ r) = r then 1 else 0 := by
    have hM : (fun r k => unitDiag (j (σ r)) r k) =
        diagonal (fun r => if j (σ r) = r then (1 : ℂ) else 0) := by
      ext r k
      by_cases hrk : r = k
      · subst hrk; simp [unitDiag, Pi.single_apply, eq_comm]
      · simp [unitDiag, diagonal_apply_ne _ hrk]
    rw [hM, det_diagonal]
    split_ifs with h
    · exact Finset.prod_eq_one fun r _ => by simp [h r]
    · simp only [not_forall] at h
      obtain ⟨r, hr⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])
  rw [mixedCoefficient]
  simp_rw [hterm]
  rw [Finset.sum_boole]
  split_ifs with hj
  · let e := Equiv.ofBijective j hj
    have : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => ∀ r, j (σ r) = r) = {e.symm} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        refine Equiv.ext fun r => ?_
        change σ r = e.symm r
        rw [Equiv.eq_symm_apply]
        exact h r
      · rintro rfl r
        exact e.apply_symm_apply r
    rw [this]
    simp
  · have : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => ∀ r, j (σ r) = r) = ∅ := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      apply hj
      have hsurj : Function.Surjective j := fun r => ⟨σ r, h r⟩
      exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
    rw [this]
    simp

/-- Two slots carrying the same diagonal unit matrix kill the mixed coefficient. -/
theorem mixedCoefficient_eq_zero_of_unitDiag (H : Fin n → Matrix (Fin n) (Fin n) ℂ) {a b : Fin n}
    (hab : a ≠ b) {k : Fin n} (ha : H a = unitDiag k) (hb : H b = unitDiag k) :
    mixedCoefficient H = 0 := by
  classical
  rw [mixedCoefficient]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hrow (r : Fin n) (hr : H (σ r) = unitDiag k) (hrk : r ≠ k) :
      ∀ c, (fun r k => H (σ r) r k) r c = 0 := by
    intro c
    simp only [hr, unitDiag]
    by_cases hrc : r = c
    · subst hrc; simp [hrk]
    · simp [diagonal_apply_ne _ hrc]
  by_cases h1 : σ.symm a = k
  · have h2 : σ.symm b ≠ k := by
      intro h2
      exact hab (σ.symm.injective (h1.trans h2.symm))
    exact det_eq_zero_of_row_eq_zero (σ.symm b) (hrow _ (by simpa using hb) h2)
  · exact det_eq_zero_of_row_eq_zero (σ.symm a) (hrow _ (by simpa using ha) h1)

/-- A diagonal matrix is the combination of the diagonal unit matrices. -/
theorem diagonal_eq_sum_unitDiag (d : Fin n → ℂ) : diagonal d = ∑ k, d k • unitDiag k := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [unitDiag, Matrix.sum_apply, Pi.single_apply]
  · simp [unitDiag, Matrix.sum_apply, diagonal_apply_ne _ hab]

/-- **Expansion of the diagonal slots.**  The slots in `P` carry `diag(d)`; expanding them over the
diagonal unit matrices gives a sum over the index choices `r i` for `i ∈ P`. -/
theorem mixedCoefficient_ite_diagonal (P : Finset (Fin n)) (d : Fin n → ℂ)
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficient (fun i => if i ∈ P then diagonal d else H i) =
      ∑ r ∈ Fintype.piFinset (fun i => if i ∈ P then (Finset.univ : Finset (Fin n)) else {i}),
        (∏ i ∈ P, d (r i)) * mixedCoefficient (fun i => if i ∈ P then unitDiag (r i) else H i)
          := by
  classical
  set g : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
    fun i k => if i ∈ P then d k • unitDiag k else H i
  have hslot : (fun i => if i ∈ P then diagonal d else H i) =
      fun i => ∑ k ∈ (if i ∈ P then (Finset.univ : Finset (Fin n)) else {i}), g i k := by
    funext i
    by_cases hi : i ∈ P
    · simp [hi, g, diagonal_eq_sum_unitDiag]
    · simp [hi, g]
  rw [← mixedCoefficientML_apply, hslot, MultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hsm : (fun i => g i (r i)) = fun i => (if i ∈ P then d (r i) else 1) •
      (if i ∈ P then unitDiag (r i) else H i) := by
    funext i
    by_cases hi : i ∈ P <;> simp [hi, g]
  rw [hsm, MultilinearMap.map_smul_univ, mixedCoefficientML_apply, smul_eq_mul]
  congr 1
  simp only [RingHom.id_apply, Finset.prod_ite_mem, Finset.univ_inter]

/-- **The permanent formula**: with every slot diagonal, the mixed coefficient is the sum over the
bijections `r` of `∏ᵢ μᵢ(r i)`. -/
theorem mixedCoefficient_diagonal_family (μ : Fin n → Fin n → ℂ) :
    mixedCoefficient (fun i => diagonal (μ i)) =
      ∑ r : Fin n → Fin n, if Function.Bijective r then ∏ i, μ i (r i) else 0 := by
  classical
  have hslot : (fun i => diagonal (μ i)) = fun i => ∑ k, μ i k • unitDiag k := by
    funext i
    exact diagonal_eq_sum_unitDiag (μ i)
  rw [← mixedCoefficientML_apply, hslot, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, mixedCoefficientML_apply, mixedCoefficient_unitDiag,
    smul_eq_mul]
  split_ifs <;> simp

/-- **Lower bound through the diagonal slots** (the expansion step of `bou02-volume:4.12 (b)`):
if every product `∏_{i ∈ P} λ(r i)` over injective index choices is at least `m`, then the mixed
coefficient with `diag(λ)` in the slots of `P` dominates `m` times the one with `1` there, as soon
as the other slots are positive semidefinite. -/
theorem le_re_mixedCoefficient_ite_diagonal (P : Finset (Fin n)) (lam : Fin n → ℝ)
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i, i ∉ P → (H i).PosSemidef) (m : ℝ)
    (hm : ∀ r : Fin n → Fin n, Set.InjOn r P → m ≤ ∏ i ∈ P, lam (r i)) :
    m * (mixedCoefficient (fun i => if i ∈ P then 1 else H i)).re ≤
      (mixedCoefficient (fun i => if i ∈ P then diagonal (fun k => (lam k : ℂ)) else H i)).re := by
  classical
  have hone : (fun i => if i ∈ P then (1 : Matrix (Fin n) (Fin n) ℂ) else H i) =
      fun i => if i ∈ P then diagonal (fun _ => (1 : ℂ)) else H i := by
    funext i; simp [diagonal_one]
  rw [hone, mixedCoefficient_ite_diagonal, mixedCoefficient_ite_diagonal, Complex.re_sum,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  set T := mixedCoefficient (fun i => if i ∈ P then unitDiag (r i) else H i)
  have hT : 0 ≤ T.re := by
    refine mixedCoefficient_re_nonneg _ fun i => ?_
    by_cases hi : i ∈ P
    · simp only [hi, ite_true]; exact unitDiag_posSemidef _
    · simp only [hi, ite_false]; exact hH i hi
  have hprod : (∏ i ∈ P, ((lam (r i) : ℝ) : ℂ)) = ((∏ i ∈ P, lam (r i) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hprod, Finset.prod_const_one, one_mul, Complex.re_ofReal_mul]
  by_cases hinj : Set.InjOn r P
  · exact mul_le_mul_of_nonneg_right (hm r hinj) hT
  · have hT0 : T = 0 := by
      simp only [Set.InjOn, not_forall] at hinj
      obtain ⟨a, ha, b, hb, hrab, hab⟩ := hinj
      exact mixedCoefficient_eq_zero_of_unitDiag _ hab (k := r a)
        (by simp [Finset.mem_coe.mp ha]) (by simp [Finset.mem_coe.mp hb, hrab])
    simp [hT0]

/-- **Upper side**: for a bijection `r`, `∏_{i ∈ Q} λ(r i)` is at most the mixed coefficient with
`diag(λ)` in the slots of `Q` and `1` elsewhere. -/
theorem prod_le_re_mixedCoefficient_ite_diagonal (Q : Finset (Fin n)) (lam : Fin n → ℝ)
    (hlam : ∀ k, 0 ≤ lam k) (r : Fin n → Fin n) (hr : Function.Bijective r) :
    ∏ i ∈ Q, lam (r i) ≤
      (mixedCoefficient (fun i => if i ∈ Q then diagonal (fun k => (lam k : ℂ)) else 1)).re := by
  classical
  set μ : Fin n → Fin n → ℝ := fun i k => if i ∈ Q then lam k else 1
  have hμ : ∀ i k, 0 ≤ μ i k := fun i k => by
    by_cases hi : i ∈ Q <;> simp [μ, hi, hlam]
  have hslot : (fun i => if i ∈ Q then diagonal (fun k => (lam k : ℂ)) else 1) =
      fun i => diagonal (fun k => ((μ i k : ℝ) : ℂ)) := by
    funext i
    by_cases hi : i ∈ Q <;> simp [μ, hi, diagonal_one]
  rw [hslot, mixedCoefficient_diagonal_family, Complex.re_sum]
  have hterm : ∀ s : Fin n → Fin n,
      ((if Function.Bijective s then ∏ i, ((μ i (s i) : ℝ) : ℂ) else 0 : ℂ)).re =
        if Function.Bijective s then ∏ i, μ i (s i) else 0 := by
    intro s
    split_ifs
    · rw [← Complex.ofReal_prod, Complex.ofReal_re]
    · simp
  simp_rw [hterm]
  have hle := Finset.single_le_sum (f := fun s : Fin n → Fin n =>
      if Function.Bijective s then ∏ i, μ i (s i) else 0)
    (fun s _ => by
      split_ifs
      · exact Finset.prod_nonneg fun i _ => hμ i (s i)
      · exact le_rfl) (Finset.mem_univ r)
  refine le_trans (le_of_eq ?_) hle
  simp only [hr, ite_true, μ]
  simp only [Finset.prod_ite_mem, Finset.univ_inter]

/-- A bijection of `Fin n` carrying a finset `Q` onto a finset `T` of the same cardinality. -/
theorem exists_perm_mapsTo (Q T : Finset (Fin n)) (hQT : Q.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i ∈ Q, σ i ∈ T := by
  classical
  have h1 : Fintype.card {x // x ∈ Q} = Fintype.card {x // x ∈ T} := by
    simp [Fintype.card_coe, hQT]
  have h2 : Fintype.card {x // x ∉ Q} = Fintype.card {x // x ∉ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    simp [Fintype.card_coe, hQT]
  let e := Fintype.equivOfCardEq h1
  let f := Fintype.equivOfCardEq h2
  refine ⟨Equiv.subtypeCongr e f, fun i hi => ?_⟩
  have : Equiv.subtypeCongr e f i = e ⟨i, hi⟩ := by
    simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hi]
  rw [this]
  exact (e ⟨i, hi⟩).2

/-- `∏_{k ∈ T} λ_k` is at most the mixed coefficient with `diag(λ)` in `|T|` slots and `1` in the
others. -/
theorem prod_le_re_mixedCoefficient_ite_diagonal' (Q T : Finset (Fin n)) (hQT : Q.card = T.card)
    (lam : Fin n → ℝ) (hlam : ∀ k, 0 ≤ lam k) :
    ∏ k ∈ T, lam k ≤
      (mixedCoefficient (fun i => if i ∈ Q then diagonal (fun k => (lam k : ℂ)) else 1)).re := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_mapsTo Q T hQT
  have hprod : ∏ i ∈ Q, lam (σ i) = ∏ k ∈ T, lam k := by
    refine Finset.prod_bij (fun i _ => σ i) hσ (fun a _ b _ h => σ.injective h) ?_
      (fun _ _ => rfl)
    have hmap : Q.map σ.toEmbedding = T :=
      Finset.eq_of_subset_of_card_le (fun k hk => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
        exact hσ i hi) (by simp [hQT])
    intro k hk
    rw [← hmap] at hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
    exact ⟨i, hi, rfl⟩
  rw [← hprod]
  exact prod_le_re_mixedCoefficient_ite_diagonal Q lam hlam σ σ.bijective

/-- **The pointwise estimate of Demailly--Păun's concentration of mass, diagonal form**
(`dp04-kahler-cone:2.6`, `bou02-volume:4.12 (a)-(c)`).  Let `λ₁, …, λₙ > 0` and `C ≥ 0`.  If the
mixed coefficient with `diag(λ)` in `n - p` slots and `1` in the other `p` is `< t`, then every
product of `n - p` of the `λ`'s is `< t`, hence every product of `p` of them exceeds `∏ λ / t`, and
the mixed coefficient with `diag(λ)` in `p` slots and `C` in the others is at least `∏ λ / t` times
the one with `1` in those `p` slots. -/
theorem diagonal_concentration_bound (lam : Fin n → ℝ) (hlam : ∀ k, 0 < lam k)
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosSemidef) (p : ℕ) (hp : p ≤ n) {t : ℝ} (ht : 0 < t)
    (h : (mixedCoefficient (fun i : Fin n =>
      if (i : ℕ) < n - p then diagonal (fun k => (lam k : ℂ)) else 1)).re < t) :
    (∏ k, lam k) / t * (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then 1 else C)).re ≤
      (mixedCoefficient (fun i : Fin n =>
        if (i : ℕ) < p then diagonal (fun k => (lam k : ℂ)) else C)).re := by
  classical
  set P : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < p
  set Q : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < n - p
  have hPc : P.card = p := by
    simp only [P, Fin.card_filter_val_lt]; omega
  have hQc : Q.card = n - p := by
    simp only [Q, Fin.card_filter_val_lt]; omega
  have hslotP (A : Matrix (Fin n) (Fin n) ℂ) :
      (fun i : Fin n => if (i : ℕ) < p then A else C) = fun i => if i ∈ P then A else C := by
    funext i; simp [P]
  have hslotQ : (fun i : Fin n => if (i : ℕ) < n - p then diagonal (fun k => (lam k : ℂ)) else 1) =
      fun i => if i ∈ Q then diagonal (fun k => (lam k : ℂ)) else 1 := by
    funext i; simp [Q]
  rw [hslotQ] at h
  rw [hslotP, hslotP]
  refine le_re_mixedCoefficient_ite_diagonal P lam (fun _ => C) (fun _ _ => hC) _ ?_
  intro r hr
  set S := P.image r
  have hSc : S.card = p := by rw [Finset.card_image_of_injOn hr, hPc]
  have hScompl : Sᶜ.card = Q.card := by
    rw [Finset.card_compl, hSc, hQc, Fintype.card_fin]
  have hlt : ∏ k ∈ Sᶜ, lam k < t :=
    (prod_le_re_mixedCoefficient_ite_diagonal' Q Sᶜ hScompl.symm lam
      (fun k => (hlam k).le)).trans_lt h
  have hS : ∏ k ∈ S, lam k = ∏ i ∈ P, lam (r i) := Finset.prod_image hr
  have hSpos : 0 < ∏ k ∈ S, lam k := Finset.prod_pos fun k _ => hlam k
  have hall : ∏ k, lam k = (∏ k ∈ S, lam k) * ∏ k ∈ Sᶜ, lam k :=
    (Finset.prod_mul_prod_compl S lam).symm
  rw [← hS, div_le_iff₀ ht, hall]
  exact (mul_lt_mul_of_pos_left hlt hSpos).le

/-- **Simultaneous diagonalization**: for positive definite `A`, `B` there is an invertible `R`
    with
`R^* B R = 1` and `R^* A R = diag(λ)`, `λ > 0`. -/
theorem exists_simultaneous_diagonalization {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    (hB : B.PosDef) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, R.det ≠ 0 ∧ star R * B * R = 1 ∧
      ∃ lam : Fin n → ℝ, (∀ k, 0 < lam k) ∧ star R * A * R = diagonal (fun k => (lam k : ℂ)) := by
  classical
  set U := hB.1.eigenvectorUnitary
  set μ := hB.1.eigenvalues
  have hμ : ∀ k, 0 < μ k := hB.eigenvalues_pos
  have hUB : star (U : Matrix (Fin n) (Fin n) ℂ) * B * U = diagonal (fun k => (μ k : ℂ)) := by
    have := hB.1.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Function.comp_def] using this
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun k => ((Real.sqrt (μ k))⁻¹ : ℂ)
  have hDstar : star D = D := by
    simp only [D, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext k
    simp [Complex.conj_ofReal]
  set R1 := (U : Matrix (Fin n) (Fin n) ℂ) * D
  have hR1B : star R1 * B * R1 = 1 := by
    simp only [R1, star_mul, hDstar]
    have : D * star (U : Matrix (Fin n) (Fin n) ℂ) * B * ((U : Matrix (Fin n) (Fin n) ℂ) * D) =
        D * (star (U : Matrix (Fin n) (Fin n) ℂ) * B * U) * D := by
      simp only [Matrix.mul_assoc]
    rw [this, hUB]
    simp only [D, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext k
    have hs : (Real.sqrt (μ k) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hμ k)).ne'
    have hsq : ((Real.sqrt (μ k) : ℂ)) * (Real.sqrt (μ k) : ℂ) = (μ k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hμ k).le]
    field_simp
    rw [← hsq]
    ring
  have hdetU : (U : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
    have h := Matrix.UnitaryGroup.star_mul_self U
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  have hdetD : D.det ≠ 0 := by
    simp only [D, det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    have : (Real.sqrt (μ k) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (hμ k)).ne'
    exact inv_ne_zero this
  have hdetR1 : R1.det ≠ 0 := by
    simp only [R1, det_mul]; exact mul_ne_zero hdetU hdetD
  have hR1inj : Function.Injective R1.mulVec := by
    intro x y hxy
    have hu : IsUnit R1.det := isUnit_iff_ne_zero.mpr hdetR1
    have := congrArg (fun v => R1⁻¹ *ᵥ v) hxy
    simpa [mulVec_mulVec, nonsing_inv_mul _ hu] using this
  set A1 := star R1 * A * R1
  have hA1 : A1.PosDef := by
    simpa [A1, star_eq_conjTranspose] using hA.conjTranspose_mul_mul_same hR1inj
  set U1 := hA1.1.eigenvectorUnitary
  set lam := hA1.1.eigenvalues
  have hU1A : star (U1 : Matrix (Fin n) (Fin n) ℂ) * A1 * U1 = diagonal (fun k => (lam k : ℂ))
    := by
    have := hA1.1.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Function.comp_def] using this
  have hdetU1 : (U1 : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
    have h := Matrix.UnitaryGroup.star_mul_self U1
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨R1 * U1, ?_, ?_, lam, hA1.eigenvalues_pos, ?_⟩
  · rw [det_mul]; exact mul_ne_zero hdetR1 hdetU1
  · rw [star_mul]
    have : star (U1 : Matrix (Fin n) (Fin n) ℂ) * star R1 * B * (R1 * U1) =
        star (U1 : Matrix (Fin n) (Fin n) ℂ) * (star R1 * B * R1) * U1 := by
      simp only [Matrix.mul_assoc]
    rw [this, hR1B, Matrix.mul_one]
    exact Matrix.UnitaryGroup.star_mul_self U1
  · rw [star_mul]
    have : star (U1 : Matrix (Fin n) (Fin n) ℂ) * star R1 * A * (R1 * U1) =
        star (U1 : Matrix (Fin n) (Fin n) ℂ) * A1 * U1 := by
      simp only [A1, Matrix.mul_assoc]
    rw [this, hU1A]

/-- Congruence of a two-pattern slot family. -/
theorem mixedCoefficient_conj_ite (R : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Prop)
    [DecidablePred c]
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficient (fun i => if c i then star R * X * R else star R * Y * R) =
      (star R).det * R.det * mixedCoefficient (fun i => if c i then X else Y) := by
  rw [← mixedCoefficient_mul_mul]
  congr 1
  funext i
  split_ifs <;> rfl

/-- **The pointwise estimate of Demailly--Păun's concentration of mass**
(`dp04-kahler-cone:2.6`, `bou02-volume:4.12 (a)-(c)`), eigenvalue-free.  Let `A`, `B` be positive
definite and `C` positive semidefinite `n × n` matrices (at a point: the coefficients of `α_ε`,
`ω_ε` and `ω`), `p ≤ n`, `t > 0`.  If the mixed coefficient of `A` in `n - p` slots and `B` in `p`
slots is `< t · det B` (the point is off the set `E_η` where the product of the `n - p` largest
eigenvalues of `A` relative to `B` is large), then

  `det A / (t · det B) · C(B[p], C[n-p]) ≤ C(A[p], C[n-p])`,

i.e. `α^p ∧ ω^{n-p} ≥ (λ₁ ⋯ λₙ / t) ω_ε^p ∧ ω^{n-p}` there. -/
theorem concentration_bound {A B C : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hC : C.PosSemidef) (p : ℕ) (hp : p ≤ n) {t : ℝ} (ht : 0 < t)
    (h : (mixedCoefficient (fun i : Fin n => if (i : ℕ) < n - p then A else B)).re <
      t * B.det.re) :
    A.det.re / (t * B.det.re) *
        (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then B else C)).re ≤
      (mixedCoefficient (fun i : Fin n => if (i : ℕ) < p then A else C)).re := by
  classical
  obtain ⟨R, hR, hRB, lam, hlam, hRA⟩ := exists_simultaneous_diagonalization hA hB
  set dr : ℝ := Complex.normSq R.det
  have hdr : 0 < dr := Complex.normSq_pos.mpr hR
  have hd : (star R).det * R.det = (dr : ℂ) := by
    rw [star_eq_conjTranspose, det_conjTranspose, Complex.normSq_eq_conj_mul_self]
    rfl
  have hC' : (star R * C * R).PosSemidef := by
    simpa [star_eq_conjTranspose] using hC.conjTranspose_mul_mul_same R
  have hdetB : B.det.re = dr⁻¹ := by
    have h1 := congrArg Matrix.det hRB
    rw [det_mul, det_mul, det_one] at h1
    have h2 : (dr : ℂ) * B.det = 1 := by rw [← hd]; linear_combination h1
    have h3 : B.det = ((dr⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr hdr.ne']
      linear_combination h2
    rw [h3, Complex.ofReal_re]
  have hdetA : A.det.re = (∏ k, lam k) / dr := by
    have h1 := congrArg Matrix.det hRA
    rw [det_mul, det_mul, det_diagonal] at h1
    have h2 : (dr : ℂ) * A.det = ((∏ k, lam k : ℝ) : ℂ) := by
      rw [← hd, Complex.ofReal_prod]; linear_combination h1
    have h3 : A.det = (((∏ k, lam k) / dr : ℝ) : ℂ) := by
      rw [Complex.ofReal_div]
      field_simp [Complex.ofReal_ne_zero.mpr hdr.ne']
      linear_combination h2
    rw [h3, Complex.ofReal_re]
  -- the three slot families after congruence
  have hQ := mixedCoefficient_conj_ite R (fun i : Fin n => (i : ℕ) < n - p) A B
  have hP1 := mixedCoefficient_conj_ite R (fun i : Fin n => (i : ℕ) < p) B C
  have hP2 := mixedCoefficient_conj_ite R (fun i : Fin n => (i : ℕ) < p) A C
  rw [hRA, hRB, hd] at hQ
  rw [hRB, hd] at hP1
  rw [hRA, hd] at hP2
  have hdiag := diagonal_concentration_bound lam hlam (star R * C * R) hC' p hp ht (by
    rw [hQ, Complex.re_ofReal_mul]
    calc dr * (mixedCoefficient fun i : Fin n => if (i : ℕ) < n - p then A else B).re
        < dr * (t * B.det.re) := mul_lt_mul_of_pos_left h hdr
      _ = t := by rw [hdetB]; field_simp)
  rw [hP1, hP2, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hdiag
  rw [hdetA, hdetB]
  have hkey : (∏ k, lam k) / dr / (t * dr⁻¹) = (∏ k, lam k) / t := by
    field_simp
  rw [hkey]
  refine le_of_mul_le_mul_left ?_ hdr
  calc dr * ((∏ k, lam k) / t *
        (mixedCoefficient fun i : Fin n => if (i : ℕ) < p then B else C).re)
      = (∏ k, lam k) / t *
        (dr * (mixedCoefficient fun i : Fin n => if (i : ℕ) < p then B else C).re) := by ring
    _ ≤ dr * (mixedCoefficient fun i : Fin n => if (i : ℕ) < p then A else C).re := hdiag

end SGPT.Foundations.Analysis.Pending.ConcentrationEigenvalueBound
