/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.StrongPotential.LeadingCoefficient

/-!
# Leading coefficients as power sums

* `T_succ`: recursion of the leading coefficients `T_k(y)`.
* `power_sum`: for distinct energies, `T_k(y) = Σ_z α_y(z) w_z^k` (divided differences).
* `top_coeff_factor`: leading coefficient of the Krylov determinant = `(Π_y α_y(y)) · Vandermonde`.
* `hstar_of_alpha`: all `α_y(y) ≠ 0` ⇒ (H*) for every interaction.
* `ps_unique`: uniqueness of power-sum coefficients (Lagrange basis; nodes may repeat).
-/

@[expose] public section

namespace DFT

section

open Polynomial Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Top coefficient of `(Hᵏ)_{y c}` (zero when `y` is out of reach). -/
noncomputable def T (A : Matrix C C ℝ) (w : C → ℝ) (d : C → ℕ) (c : C) (k : ℕ) (y : C) : ℝ :=
  if d y ≤ k then ((Hl A 0 w ^ k) y c).coeff (k - d y) else 0

lemma T_zero {A : Matrix C C ℝ} (w : C → ℝ) {d : C → ℕ} {c : C} (hc : d c = 0) (y : C) :
    T A w d c 0 y = if y = c then 1 else 0 := by
  unfold T
  by_cases hy : y = c
  · subst hy; simp [hc]
  · by_cases hd : d y ≤ 0
    · simp [hd, hy]
    · simp [hd, hy]

lemma T_succ {A : Matrix C C ℝ} (w : C → ℝ) {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (k : ℕ) (y : C) :
    T A w d c (k + 1) y = w y * T A w d c k y +
      ∑ z ∈ Finset.univ.erase y, (if d z + 1 = d y then A y z * T A w d c k z else 0) := by
  unfold T
  by_cases hy : d y ≤ k + 1
  · rw [ite_eq_left hy, pow_succ_coeff]
    have e1 : ((Hl A 0 w ^ k) y c).coeff (k + 1 - d y) = 0 := entry_bound hL hc 0 w k y _ (by omega)
    rw [e1, mul_zero, zero_add]
    congr 1
    · by_cases h1 : d y ≤ k
      · rw [ite_eq_right (by omega), ite_eq_left h1, show k + 1 - d y - 1 = k - d y by omega]
      · rw [ite_eq_left (by omega), ite_eq_right h1, mul_zero]
    · apply Finset.sum_congr rfl
      intro z hz
      by_cases hA : A y z = 0
      · simp [hA]
      · have hlip := hL y z (Finset.mem_erase.mp hz).1.symm hA
        by_cases hdz : d z + 1 = d y
        · have : k + 1 - d y = k - d z := by omega
          rw [ite_eq_left hdz, ite_eq_left (by omega), this]
        · rw [ite_eq_right hdz, entry_bound hL hc 0 w k z _ (by omega), mul_zero]
  · rw [ite_eq_right hy]
    have h1 : ¬ d y ≤ k := by omega
    rw [ite_eq_right h1, mul_zero, zero_add]
    symm
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hdz : d z + 1 = d y
    · rw [ite_eq_left hdz, ite_eq_right (show ¬ d z ≤ k by omega), mul_zero]
    · rw [ite_eq_right hdz]

/-- **Power-sum (divided-difference) representation of the top coefficients.** -/
theorem power_sum {A : Matrix C C ℝ} (w : C → ℝ) (hw : Function.Injective w) {d : C → ℕ}
    (hL : Lip A d)
    {c : C} (hc : d c = 0) :
    ∀ n, ∀ y, d y = n → ∃ α : C → ℝ, (∀ z, α z ≠ 0 → z = y ∨ d z < d y) ∧
      ∀ k, T A w d c k y = ∑ z, α z * w z ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hy
  -- representations for the predecessors
  have hpred : ∀ p, d p < n → ∃ α : C → ℝ, (∀ z, α z ≠ 0 → z = p ∨ d z < d p) ∧
      ∀ k, T A w d c k p = ∑ z, α z * w z ^ k := fun p hp => ih (d p) hp p rfl
  choose! αp hαsupp hαrep using hpred
  -- the source term for z ≠ y
  set S : C → ℝ := fun z => ∑ p ∈ Finset.univ.erase y,
    (if d p + 1 = d y then A y p * αp p z else 0)
  set β : C → ℝ := fun z => if z = y then (if y = c then 1 else 0) - ∑ z' ∈ Finset.univ.erase y,
      S z' / (w z' - w y) else S z / (w z - w y)
  refine ⟨β, ?_, ?_⟩
  · intro z hz
    by_cases hzy : z = y
    · exact Or.inl hzy
    · right
      have hS : S z ≠ 0 := by
        intro h0; apply hz; simp [β, hzy, h0]
      obtain ⟨p, hp, hp2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
      split_ifs at hp2 with hdp
      · have hα : αp p z ≠ 0 := by intro h0; apply hp2; rw [h0, mul_zero]
        rcases hαsupp p (by omega) z hα with h | h
        · subst h; omega
        · omega
      · exact absurd rfl hp2
  · -- S y = 0 : predecessors' representations do not involve y
    have hSy : S y = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      split_ifs with hdp
      · have : αp p y = 0 := by
          by_contra hne
          rcases hαsupp p (by omega) y hne with h | h
          · exact (Finset.mem_erase.mp hp).1 h.symm
          · omega
        rw [this, mul_zero]
      · rfl
    have hβ : ∀ z, z ≠ y → β z * (w z - w y) = S z := by
      intro z hz
      have : w z - w y ≠ 0 := sub_ne_zero.mpr (fun h => hz (hw h))
      simp [β, hz]; field_simp
    have hsumβ : ∑ z, β z = if y = c then 1 else 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
      simp only [β, ite_eq_left rfl]
      rw [Finset.sum_congr rfl (fun z hz => ite_eq_right (Finset.mem_erase.mp hz).1)]
      ring
    intro k
    induction k with
    | zero => rw [T_zero w hc]; simp [hsumβ]
    | succ k ihk =>
      rw [T_succ w hL hc, ihk]
      have hpk : ∀ p ∈ Finset.univ.erase y, (if d p + 1 = d y then A y p * T A w d c k p else 0) =
          ∑ z, (if d p + 1 = d y then A y p * αp p z else 0) * w z ^ k := by
        intro p _
        split_ifs with hdp
        · rw [hαrep p (by omega) k, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro z _; ring
        · simp
      rw [Finset.sum_congr rfl hpk, Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_mul]
      change w y * (β z * w z ^ k) + S z * w z ^ k = β z * w z ^ (k + 1)
      by_cases hzy : z = y
      · subst hzy; rw [hSy]; ring
      · rw [← hβ z hzy]; ring

/-- The chosen divided-difference coefficients `α_y`. -/
noncomputable def alphaRep (A : Matrix C C ℝ) (w : C → ℝ) (hw : Function.Injective w) (d : C → ℕ)
    (hL : Lip A d) (c : C) (hc : d c = 0) (y : C) : C → ℝ :=
  Classical.choose (power_sum w hw hL hc (d y) y rfl)

lemma alphaRep_supp {A : Matrix C C ℝ} {w : C → ℝ} (hw : Function.Injective w) {d : C → ℕ}
    (hL : Lip A d) {c : C} (hc : d c = 0) (y z : C) :
    alphaRep A w hw d hL c hc y z ≠ 0 → z = y ∨ d z < d y :=
  (Classical.choose_spec (power_sum w hw hL hc (d y) y rfl)).1 z

lemma alphaRep_rep {A : Matrix C C ℝ} {w : C → ℝ} (hw : Function.Injective w) {d : C → ℕ}
    (hL : Lip A d) {c : C} (hc : d c = 0) (y : C) (k : ℕ) :
    T A w d c k y = ∑ z, alphaRep A w hw d hL c hc y z * w z ^ k :=
  (Classical.choose_spec (power_sum w hw hL hc (d y) y rfl)).2 k

/-- A matrix that is "triangular with respect to `d`" has determinant equal to its diagonal product.
-/
lemma det_triangular_d (Mx : Matrix C C ℝ) (d : C → ℕ) (h : ∀ y z, Mx y z ≠ 0 → z = y ∨ d z < d y) :
    Mx.det = ∏ y, Mx y y := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    have : ∏ i, Mx (σ i) i = 0 := by
      by_contra hne
      have hall : ∀ i, i = σ i ∨ d i < d (σ i) := fun i =>
        h (σ i) i (fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ i) h0))
      obtain ⟨i0, hi0⟩ : ∃ i, σ i ≠ i := by
        by_contra hfix; push Not at hfix; exact hσ (Equiv.ext hfix)
      have hlt : ∑ i, d i < ∑ i, d (σ i) := by
        apply Finset.sum_lt_sum
        · intro i _; rcases hall i with h' | h'
          · exact le_of_eq (congrArg d h')
          · exact h'.le
        · exact ⟨i0, Finset.mem_univ _, (hall i0).resolve_left (fun h' => hi0 h'.symm)⟩
      rw [Equiv.sum_comp σ d] at hlt
      exact lt_irrefl _ hlt
    rw [this, smul_zero]
  · intro h0; exact absurd (Finset.mem_univ _) h0

/-- **Leading coefficient = (triangular) × (Vandermonde).** With `ord` an enumeration of `C`,
the top coefficient of the free Krylov determinant equals `(Π_y α_y(y)) · det[w_z ^ ord j]`. -/
theorem top_coeff_factor {A : Matrix C C ℝ} {w : C → ℝ} (hw : Function.Injective w) {d : C → ℕ}
    (hL : Lip A d) {c : C} (hc : d c = 0) (ord : C → ℕ) :
    (kry (Hl A 0 w) c ord).det.coeff (∑ j, ord j - ∑ y, d y) =
      (∏ y, alphaRep A w hw d hL c hc y y) * (Matrix.of fun z j => w z ^ ord j).det := by
  set α := fun y z => alphaRep A w hw d hL c hc y z
  have hN : (kry (Hl A 0 w) c ord).det.coeff (∑ j, ord j - ∑ y, d y) =
      (Matrix.of fun y j => T A w d c (ord j) y).det := by
    simpa only [T] using det_coeff_eq hL hc 0 w ord
  have hfac : (Matrix.of fun y j => T A w d c (ord j) y) =
      (Matrix.of fun y z => α y z) * (Matrix.of fun z j => w z ^ ord j) := by
    ext y j
    simp [Matrix.mul_apply, alphaRep_rep hw hL hc, α]
  rw [hN, hfac, Matrix.det_mul,
    det_triangular_d _ d (fun y z h => alphaRep_supp hw hL hc y z (by simpa [α] using h))]
  simp [α]

/-- The Vandermonde factor is nonzero when `ord` enumerates `C` and the energies are distinct. -/
lemma vandermonde_factor_ne_zero {w : C → ℝ} (hw : Function.Injective w) :
    (Matrix.of fun z j => w z ^ ((Fintype.equivFin C j : ℕ))).det ≠ 0 := by
  set e := Fintype.equivFin C
  have : (Matrix.of fun z j => w z ^ ((e j : ℕ))) =
      (Matrix.vandermonde (w ∘ e.symm)).submatrix e e := by
    ext z j; simp [Matrix.vandermonde]
  rw [this, Matrix.det_submatrix_equiv_self]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr (hw.comp e.symm.injective)

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Reduction of (H*) to the diagonal path sums.** Along a direction `u` with pairwise distinct
configuration energies `w y = Σ_i u_i n_i(y)`, if every diagonal divided-difference coefficient
`α_y(y)` is nonzero, then the Krylov polynomial of configuration `c` is nonzero for every
interaction `Vint`. -/
theorem hstar_of_alpha {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (n : V → C → ℝ) (u : V → ℝ) (hw : Function.Injective (fun y => ∑ i, u i * n i y))
    (hα : ∀ y, alphaRep A _ hw d hL c hc y y ≠ 0) (Vint : C → ℝ) :
    krylovPoly (A + Matrix.diagonal Vint) n c (fun j => (Fintype.equivFin C j : ℕ)) ≠ 0 := by
  apply krylovPoly_ne_zero_of_top hL hc n u
  rw [top_coeff_factor hw hL hc]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun y _ => hα y)) (vandermonde_factor_ne_zero hw)

end

section
open Polynomial

lemma eval_weighted_sum {K : Type*} [Fintype K] (p : ℝ[X]) (c z : K → ℝ) :
    ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * ∑ i, c i * z i ^ k =
        ∑ i, c i * p.eval (z i) := by
  simp_rw [Finset.mul_sum, Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _; ring

/-- **Uniqueness of power-sum coefficients** (nodes may repeat). -/
theorem ps_unique {I J : Type*} [Fintype I] [Fintype J] (a x : I → ℝ) (b y : J → ℝ)
    (h : ∀ k : ℕ, ∑ i, a i * x i ^ k = ∑ j, b j * y j ^ k) (v : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => x i = v), a i =
        ∑ j ∈ Finset.univ.filter (fun j => y j = v), b j := by
  classical
  set S : Finset ℝ := (Finset.univ.image x ∪ Finset.univ.image y).erase v
  set p : ℝ[X] := Polynomial.C (∏ s ∈ S, (v - s))⁻¹ * ∏ s ∈ S, (X - Polynomial.C s)
  have hv : p.eval v = 1 := by
    have hne : ∏ s ∈ S, (v - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun s hs =>
      sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hs).1 h.symm))
    simp [p, Polynomial.eval_prod, hne]
  have hs : ∀ s, s ≠ v → (s ∈ Finset.univ.image x ∪ Finset.univ.image y) → p.eval s = 0 := by
    intro s hsv hsS
    simp only [p, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X]
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hsv, hsS⟩) (sub_self s), mul_zero]
  have hA : ∑ i, a i * p.eval (x i) = ∑ i ∈ Finset.univ.filter (fun i => x i = v), a i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro i _
    split_ifs with hxi
    · rw [hxi, hv, mul_one]
    · rw [hs (x i) hxi (Finset.mem_union_left _ (Finset.mem_image_of_mem x (Finset.mem_univ i))),
        mul_zero]
  have hB : ∑ j, b j * p.eval (y j) = ∑ j ∈ Finset.univ.filter (fun j => y j = v), b j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro j _
    split_ifs with hyj
    · rw [hyj, hv, mul_one]
    · rw [hs (y j) hyj (Finset.mem_union_right _ (Finset.mem_image_of_mem y (Finset.mem_univ j))),
        mul_zero]
  rw [← hA, ← hB, ← eval_weighted_sum, ← eval_weighted_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [h k]

end

end DFT
