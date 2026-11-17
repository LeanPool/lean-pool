/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.InverseSqrt
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Coordinate
/-!
# Cumulant energies and the middle term `L_m` of the localization

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (72) and (75)–(76), at a fixed law `ν` with covariance `A`
and
`σ = A^{-1/2}`: the middle term `L_m(h) = Σ_{J ∋ i₀, 2 ≤ |J|, |Jᶜ| ≥ 2} ⟪κ_{|J|+1}(h_J, ·), A⁻¹
κ_{m−|J|+1}(h_{Jᶜ}, ·)⟫`
(`lowerDrift`, in the mask form of `Analysis/BakryEmery/Cumulant/Leibniz.lean`) and the cumulant
energy
`E_{r+1} = |κ_{r+1}(u)|²_A = Σ_J κ_{r+1}(u, σ e_{J_1}, …, σ e_{J_r})²` (`cumulantEnergy`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.BKL

variable {n : ℕ}

/--
The middle term `L_m` of BKL arXiv:2610.05474v1, (72), at a fixed law `ν` with covariance `A`:
`L_m(h) = Σ_{J ∋ i₀, 2 ≤ |J|, |Jᶜ| ≥ 2} ⟪κ_{|J|+1}(h_J, ·), A⁻¹ κ_{m−|J|+1}(h_{Jᶜ}, ·)⟫` (slot `i₀ =
0`). -/
def lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) {m : ℕ}
    (h : Fin m → EuclideanSpace ℝ (Fin n)) (i₀ : Fin m) : ℝ :=
  ∑
    q ∈
      Finset.univ.filter
        (fun q : Fin m → Bool =>
          q i₀ = true ∧ 2 ≤ (selected h q).length ∧ 2 ≤ (selected h (fun i => !(q i))).length),
    ⟪cumulantVector ν (selected h q),
      Ring.inverse (Covariance.operator ν) (cumulantVector ν (selected h (fun i => !(q i))))⟫

/--
The cumulant energy `E_{r+1} = |κ_{r+1}(u)|²_A = Σ_J κ_{r+1}(u, σ e_{J_1}, …, σ e_{J_r})²`, `σ =
A^{-1/2}`
(BKL (75)–(76)). -/
def cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ J : Fin r → Fin n,
    cumulant ν (r + 1)
        (Fin.cons u fun k =>
          inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^
      2

end FunctionalInequalities.KLS.BKL

section PointwiseCumulantEnergy

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

/-! Section 6 pointwise bound (BKL (99)–(102) and the pointwise triangle inequality behind (104)):
`sqrt_lowerDrift_energy_le`. -/

namespace FunctionalInequalities.KLS.BKL

variable {n : ℕ}

section Masks

/-! Boolean-mask combinatorics for the ordered selector `selected`: one-step unfolding, the number
of selected
slots (`maskCount`), its complement rule, and the binomial count of the masks containing slot `0`.
-/

theorem selected_succ {E : Type*} {k : ℕ} (h : Fin (k + 1) → E) (q : Fin (k + 1) → Bool) :
    selected h q =
      if q 0 = true then h 0 :: selected (Fin.tail h) (Fin.tail q)
      else selected (Fin.tail h) (Fin.tail q) := by
  simp [selected]

theorem selected_zero {E : Type*} (h : Fin 0 → E) (q : Fin 0 → Bool) : selected h q = [] := by
  simp [selected]

/-- number of selected slots -/
def maskCount {k : ℕ} (q : Fin k → Bool) : ℕ := (Finset.univ.filter fun i => q i = true).card

theorem maskCount_succ {k : ℕ} (q : Fin (k + 1) → Bool) :
    maskCount q = (if q 0 = true then 1 else 0) + maskCount (Fin.tail q) := by
  rw [maskCount, maskCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl

theorem maskCount_zero (q : Fin 0 → Bool) : maskCount q = 0 := by
  simp [maskCount]

theorem tail_not {k : ℕ} (q : Fin (k + 1) → Bool) :
    Fin.tail (fun i => !(q i)) = fun i => !(Fin.tail q i) :=
  rfl

theorem maskCount_add_compl {k : ℕ} (q : Fin k → Bool) :
    maskCount q + maskCount (fun i => !(q i)) = k := by
  induction k with
  | zero => simp [maskCount_zero]
  | succ k ih =>
    rw [maskCount_succ, maskCount_succ (fun i => !(q i)), tail_not]
    have := ih (Fin.tail q)
    cases q 0 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
      omega

theorem selected_length {E : Type*} {k : ℕ} (h : Fin k → E) (q : Fin k → Bool) :
    (selected h q).length = maskCount q := by
  induction k with
  | zero => simp [selected_zero, maskCount_zero]
  | succ k ih =>
    rw [selected_succ, maskCount_succ]
    cases hq : q 0 <;> simp [ih, add_comm]

theorem sum_cons_split {ι : Type*} [Fintype ι] {k : ℕ} (F : (Fin (k + 1) → ι) → ℝ) :
    ∑ J : Fin (k + 1) → ι, F J = ∑ j : ι, ∑ J' : Fin k → ι, F (Fin.cons j J') := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_snoc_split {ι : Type*} [Fintype ι] {k : ℕ} (F : (Fin (k + 1) → ι) → ℝ) :
    ∑ J : Fin (k + 1) → ι, F J = ∑ j : ι, ∑ J' : Fin k → ι, F (Fin.snoc J' j) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => ι)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_fin_zero {ι : Type*} [Fintype ι] (F : (Fin 0 → ι) → ℝ) :
    ∑ J : Fin 0 → ι, F J = F (fun i => i.elim0) := by
  rw [Fintype.sum_unique]
  congr

theorem card_masks (k c : ℕ) :
    (Finset.univ.filter fun q : Fin k → Bool => maskCount q = c).card = k.choose c := by
  classical
  have h := Finset.card_powersetCard c (Finset.univ : Finset (Fin k))
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.card_nbij' (fun q => Finset.univ.filter fun i => q i = true)
    (fun s i => decide (i ∈ s)) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hq.2⟩
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change (Finset.univ.filter fun i => decide (i ∈ s) = true).card = c
    rw [← hs.2]
    congr 1
    ext i
    simp
  · intro q _
    funext i
    simp
  · intro s _
    ext i
    simp

theorem card_masks_true (k c : ℕ) :
    (Finset.univ.filter fun q : Fin (k + 1) → Bool => q 0 = true ∧ maskCount q = c + 1).card =
      k.choose c := by
  classical
  rw [← card_masks k c]
  refine Finset.card_nbij' (fun q => Fin.tail q) (fun q => Fin.cons true q) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h2 := hq.2.2
    rw [maskCount_succ, hq.2.1] at h2
    simp only [ite_true] at h2
    change maskCount (Fin.tail q) = c
    omega
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [maskCount_succ]
    simp [hq.2, add_comm]
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    simp only
    rw [← hq.2.1]
    exact Fin.cons_self_tail q
  · intro q _
    simp only
    simp

/--
Reindex a mask-selected sum as a double sum over the selected and the complementary slots. -/
theorem sum_selected_eq {E ι : Type*} [Fintype ι] (w : ι → E) :
    ∀ (k : ℕ) (q : Fin k → Bool) (G : List E → List E → ℝ) (c₁ c₂ : ℕ),
      maskCount q = c₁ →
        maskCount (fun i => !(q i)) = c₂ →
          ∑ J : Fin k → ι,
              G (selected (fun i => w (J i)) q)
                (selected (fun i => w (J i)) (fun i => !(q i))) =
            ∑ J₁ : Fin c₁ → ι,
              ∑ J₂ : Fin c₂ → ι,
                G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i)) := by
  intro k
  induction k with
  | zero =>
    intro q G c₁ c₂ h1 h2
    rw [maskCount_zero] at h1 h2
    subst h1
    subst h2
    simp [selected_zero, List.ofFn_zero]
  | succ k ih =>
    intro q G c₁ c₂ h1 h2
    rw [sum_cons_split]
    rw [maskCount_succ] at h1
    rw [maskCount_succ, tail_not] at h2
    have hsel :
      ∀ (j : ι) (J' : Fin k → ι) (p : Fin (k + 1) → Bool),
        selected (fun i => w ((Fin.cons j J' : Fin (k + 1) → ι) i)) p =
          if p 0 = true then w j :: selected (fun i => w (J' i)) (Fin.tail p)
          else selected (fun i => w (J' i)) (Fin.tail p) := by
      intro j J' p
      have ht :
        Fin.tail (fun i => w ((Fin.cons j J' : Fin (k + 1) → ι) i)) = fun i => w (J' i) := by
        funext i
        simp [Fin.tail]
      rw [selected_succ, ht]
      simp
    simp only [hsel, tail_not]
    cases hq : q 0 with
    |
      true =>
      simp only [hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, zero_add] at h1 h2 ⊢
      rw [add_comm] at h1
      subst h1
      rw [sum_cons_split (k := maskCount (Fin.tail q))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ih (Fin.tail q) (fun l₁ l₂ => G (w j :: l₁) l₂) _ _ rfl h2]
      refine Finset.sum_congr rfl fun J₁ _ => ?_
      refine Finset.sum_congr rfl fun J₂ _ => ?_
      simp [List.ofFn_succ]
    |
      false =>
      simp only [hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte, zero_add] at h1 h2 ⊢
      rw [add_comm] at h2
      subst h1
      subst h2
      symm
      calc
        ∑ J₁ : Fin (maskCount (Fin.tail q)) → ι,
              ∑ J₂ : Fin (maskCount (fun i => !(Fin.tail q i)) + 1) → ι,
                G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i)) =
            ∑ J₁ : Fin (maskCount (Fin.tail q)) → ι,
              ∑ j : ι,
                ∑ J₂ : Fin (maskCount (fun i => !(Fin.tail q i))) → ι,
                  G (List.ofFn fun i => w (J₁ i)) (w j :: List.ofFn fun i => w (J₂ i)) := by
          refine Finset.sum_congr rfl fun J₁ _ => ?_
          rw [sum_cons_split]
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun J₂ _ => ?_
          simp [List.ofFn_succ]
        _ =
            ∑ j : ι,
              ∑ J₁ : Fin (maskCount (Fin.tail q)) → ι,
                ∑ J₂ : Fin (maskCount (fun i => !(Fin.tail q i))) → ι,
                  G (List.ofFn fun i => w (J₁ i)) (w j :: List.ofFn fun i => w (J₂ i)) :=
          Finset.sum_comm
        _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ih (Fin.tail q) (fun l₁ l₂ => G l₁ (w j :: l₂)) _ _ rfl rfl]

/-- Minkowski / ℓ² triangle inequality for finite sums of squares. -/
theorem sqrt_sum_sq_sum_le {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℝ) :
    Real.sqrt (∑ i, (∑ q ∈ s, f q i) ^ 2) ≤ ∑ q ∈ s, Real.sqrt (∑ i, f q i ^ 2) := by
  let x : κ → EuclideanSpace ℝ ι := fun q => WithLp.toLp 2 (f q)
  have hn : ∀ q, ‖x q‖ = Real.sqrt (∑ i, f q i ^ 2) := by
    intro q
    rw [EuclideanSpace.norm_eq]
    simp [x, Real.norm_eq_abs, sq_abs]
  have hs : ‖∑ q ∈ s, x q‖ = Real.sqrt (∑ i, (∑ q ∈ s, f q i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [x, Real.norm_eq_abs, sq_abs]
  calc Real.sqrt (∑ i, (∑ q ∈ s, f q i) ^ 2) = ‖∑ q ∈ s, x q‖ := hs.symm
    _ ≤ ∑ q ∈ s, ‖x q‖ := norm_sum_le s x
    _ = ∑ q ∈ s, Real.sqrt (∑ i, f q i ^ 2) := Finset.sum_congr rfl fun q _ => hn q


end Masks

section Algebra

/-! The whitened frame `w_j = σ e_j` with `σ = A^{-1/2}`: `Σ_j ⟪z, w_j⟫⟪y, w_j⟫ = ⟪z, A⁻¹ y⟫`, `Σ_j
v_j w_j = σ v`,
`⟪A σ v, σ v⟫ = |v|²`, the cumulant Riesz vector on `List.ofFn`, and the rotation `κ(g, x) = κ(x,
g)`. -/

/-- `σ e_j` -/
def sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (j : Fin n) : EuclideanSpace ℝ (Fin n) :=
  inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ j)

theorem covariance_isPositive (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) :
    (Covariance.operator ν).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨Covariance.operator_isSelfAdjoint _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (hApos v hv).le

theorem inverseSqrt_inner_left (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪inverseSqrt (Covariance.operator ν) x, y⟫ = ⟪x, inverseSqrt (Covariance.operator ν) y⟫ := by
  have hsa := (inverseSqrt_spec _ (covariance_isPositive ν hApos) hA).2.1
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) x y

theorem inner_sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (z : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : ⟪z, sigmaBasis ν j⟫ = inverseSqrt (Covariance.operator ν) z j := by
  unfold sigmaBasis
  rw [← inverseSqrt_inner_left ν hA hApos, EuclideanSpace.inner_basisFun_real]

theorem sum_inner_sigmaBasis_mul (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (z y : EuclideanSpace ℝ (Fin n)) :
    ∑ j, ⟪z, sigmaBasis ν j⟫ * ⟪y, sigmaBasis ν j⟫ =
      ⟪z, Ring.inverse (Covariance.operator ν) y⟫ := by
  have hsq := (inverseSqrt_spec _ (covariance_isPositive ν hApos) hA).2.2.1
  have h :=
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner
      (inverseSqrt (Covariance.operator ν) z) (inverseSqrt (Covariance.operator ν) y)
  simp only [EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_inner] at h
  simp only [inner_sigmaBasis ν hA hApos]
  rw [h, inverseSqrt_inner_left ν hA hApos, ← mul_apply_eq_comp, hsq]

theorem sum_mul_inner_sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (y : EuclideanSpace ℝ (Fin n))
    (v : Fin n → ℝ) :
    ∑ j, v j * ⟪y, sigmaBasis ν j⟫ =
      ⟪y, inverseSqrt (Covariance.operator ν) (WithLp.toLp 2 v)⟫ := by
  rw [← inverseSqrt_inner_left ν hA hApos]
  simp only [inner_sigmaBasis ν hA hApos, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem inner_cov_inverseSqrt_eq_sum (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (v : Fin n → ℝ) :
    ⟪Covariance.operator ν (inverseSqrt (Covariance.operator ν) (WithLp.toLp 2 v)),
      inverseSqrt (Covariance.operator ν) (WithLp.toLp 2 v)⟫ = ∑ j, v j ^ 2 := by
  rw [← inverseSqrt_inner_left ν hA hApos, ← mul_apply_eq_comp,
    ← mul_apply_eq_comp,
    inverseSqrt_mul_mul_inverseSqrt _ (covariance_isPositive ν hApos) hA]
  simp only [one_apply_eq_self, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [sq]

theorem inner_cumulantVector_ofFn (μ : Measure (EuclideanSpace ℝ (Fin n))) {c : ℕ}
    (g : Fin c → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪cumulantVector μ (List.ofFn g), x⟫ = cumulant μ (c + 1) (Fin.snoc g x) := by
  rw [cumulantVector_inner]
  have haux : ∀ (N : ℕ) (hN : N = c) (g' : Fin N → EuclideanSpace ℝ (Fin n)),
      (∀ i, g' i = g (Fin.cast hN i)) →
        cumulant μ (N + 1) (Fin.snoc g' x) = cumulant μ (c + 1) (Fin.snoc g x) := by
    intro N hN g' hg'
    subst hN
    have : g' = g := by
      funext i
      simpa using hg' i
    rw [this]
  exact haux _ (List.length_ofFn (f := g)) _ (fun i => List.get_ofFn g i)

theorem cumulant_snoc_eq_cons (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support) {c : ℕ}
    (g : Fin c → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) (Fin.snoc g x) =
      cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) (Fin.cons x g) := by
  have h : (Fin.snoc g x : Fin (c + 1) → EuclideanSpace ℝ (Fin n)) =
      (Fin.cons x g : Fin (c + 1) → EuclideanSpace ℝ (Fin n)) ∘ finRotate (c + 1) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.coeSucc_eq_succ]
  rw [h, cumulant_comp_perm_of_compact ν hc]


/-- One mask summand of `lowerDrift`. -/
def maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (q : Fin m → Bool) : ℝ :=
  ⟪cumulantVector ν (selected h q),
    Ring.inverse (Covariance.operator ν) (cumulantVector ν (selected h (fun i => !(q i))))⟫

/-- The masks of the middle allocations: slot `0` selected, at least two slots on each side. -/
def middleMasks (k : ℕ) : Finset (Fin (k + 1) → Bool) :=
  Finset.univ.filter fun q => q 0 = true ∧ 2 ≤ maskCount q ∧ 2 ≤ maskCount (fun i => !(q i))

theorem lowerDrift_eq_sum_middleMasks (ν : Measure (EuclideanSpace ℝ (Fin n))) {k : ℕ}
    (h : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) :
    lowerDrift ν h 0 = ∑ q ∈ middleMasks k, maskTerm ν h q := by
  unfold lowerDrift middleMasks maskTerm
  simp only [selected_length]

/-- The squared pair term `⟪κ(u, l₁, ·), A⁻¹ κ(l₂, ·)⟫²` as a function of the two selected lists. -/
def pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n))
    (l₁ l₂ : List (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⟪cumulantVector ν (u :: l₁), Ring.inverse (Covariance.operator ν) (cumulantVector ν l₂)⟫ ^ 2

/--
**Row contraction for one mask** (BKL (101)–(102)): with `c` selected and `c₂` complementary slots,
`Σ_{J₁, J₂} ⟪κ_{c+2}(u, w_{J₁}, ·), A⁻¹ κ_{c₂+1}(w_{J₂}, ·)⟫² ≤ β E_{c+2}(u)` whenever
`E_{c₂+1}(v) ≤ β ⟪A v, v⟫` for every `v` (hypothesis (100) at order `c₂ + 1`). -/
theorem sum_sq_pairTerm_ofFn_le (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos :
      ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    {c c₂ : ℕ} (β : ℝ)
    (h100 :
      ∀ v : EuclideanSpace ℝ (Fin n),
        cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) c₂ v ≤
          β * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑ J₁ : Fin c → Fin n,
        ∑ J₂ : Fin c₂ → Fin n,
          pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u
            (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₁ i))
            (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)) ≤
      β * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) u := by
  simp only [pairTerm, ← List.ofFn_cons, ← sum_inner_sigmaBasis_mul _ hA hApos]
  refine
    le_trans
      (Tensor.sum_sq_contract_le (b := β)
        (fun (J₂ : Fin c₂ → Fin n) (j : Fin n) =>
          ⟪cumulantVector (ν : Measure (EuclideanSpace ℝ (Fin n)))
              (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)),
            sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) j⟫)
        ?_
        (fun (J₁ : Fin c → Fin n) (j : Fin n) =>
          ⟪cumulantVector (ν : Measure (EuclideanSpace ℝ (Fin n)))
              (List.ofFn
                (Fin.cons u fun i =>
                  sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₁ i))),
            sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) j⟫))
      (le_of_eq ?_)
  · intro v
    have h1 :
      ∀ J₂ : Fin c₂ → Fin n,
        ∑ j,
            v j *
              ⟪cumulantVector (ν : Measure (EuclideanSpace ℝ (Fin n)))
                  (List.ofFn fun i =>
                    sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)),
                sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) j⟫ =
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (c₂ + 1)
            (Fin.cons
              (inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (WithLp.toLp 2 v))
              fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)) := by
      intro J₂
      rw [sum_mul_inner_sigmaBasis _ hA hApos, inner_cumulantVector_ofFn,
        cumulant_snoc_eq_cons ν hc]
    simp only [h1]
    have h2 :=
      h100
        (inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
          (WithLp.toLp 2 v))
    rw [inner_cov_inverseSqrt_eq_sum _ hA hApos] at h2
    exact h2
  · congr 1
    unfold cumulantEnergy
    rw [sum_snoc_split, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J₁ _ => ?_
    rw [inner_cumulantVector_ofFn, ← Fin.cons_snoc_eq_snoc_cons]
    congr 3
    exact (Fin.comp_snoc (sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n)))) J₁ j).symm

/-- The Section 6 pointwise bound with `m = k + 1`. -/
theorem sqrt_sum_lowerDrift_sq_le_aux (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos :
      ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (k : ℕ) (b : ℕ → ℝ)
    (h100 :
      ∀ r,
        2 ≤ r →
          r < k + 1 →
            ∀ v : EuclideanSpace ℝ (Fin n),
              cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r - 1) v ≤
                b r * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt
        (∑ J : Fin k → Fin n,
          lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n)))
              (Fin.cons u fun i =>
                  inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                    (EuclideanSpace.basisFun (Fin n) ℝ (J i)) :
                Fin (k + 1) → EuclideanSpace ℝ (Fin n))
              0 ^
            2) ≤
      ∑ a ∈ Finset.Icc 2 (k - 1),
        (k.choose (a - 1) : ℝ) *
          Real.sqrt
            (b (k + 2 - a) * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) := by
  change
    Real.sqrt
        (∑ J : Fin k → Fin n,
          lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n)))
              (Fin.cons u fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
                Fin (k + 1) → EuclideanSpace ℝ (Fin n))
              0 ^
            2) ≤
      _
  simp only [lowerDrift_eq_sum_middleMasks]
  have hmaps : ∀ q ∈ middleMasks k, maskCount q ∈ Finset.Icc 2 (k - 1) := by
    intro q hq
    rw [middleMasks, Finset.mem_filter] at hq
    have := maskCount_add_compl q
    rw [Finset.mem_Icc]
    omega
  have hcard :
    ∀ a ∈ Finset.Icc 2 (k - 1),
      ((middleMasks k).filter fun q => maskCount q = a).card = k.choose (a - 1) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel, ← card_masks_true k a']
    congr 1
    ext q
    simp only [middleMasks, Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    have := maskCount_add_compl q
    constructor
    · rintro ⟨⟨h0, -, -⟩, h⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨h0, by omega, by omega⟩, h⟩
  have hmask :
    ∀ q ∈ middleMasks k,
      ∑ J : Fin k → Fin n,
          maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n)))
              (Fin.cons u fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
                Fin (k + 1) → EuclideanSpace ℝ (Fin n))
              q ^
            2 ≤
        b (k + 2 - maskCount q) *
          cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (maskCount q) u := by
    intro q hq
    rw [middleMasks, Finset.mem_filter] at hq
    obtain ⟨-, hq0, hq2, hq2'⟩ := hq
    have hcnt := maskCount_succ q
    simp only [hq0, ↓reduceIte] at hcnt
    have hcnt' := maskCount_succ (fun i => !(q i))
    rw [tail_not] at hcnt'
    simp only [hq0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, zero_add] at hcnt'
    have hsum := maskCount_add_compl (Fin.tail q)
    have hterm :
      ∀ J : Fin k → Fin n,
        maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n)))
              (Fin.cons u fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
                Fin (k + 1) → EuclideanSpace ℝ (Fin n))
              q ^
            2 =
          pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u
            (selected (fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i))
              (Fin.tail q))
            (selected (fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i))
              (fun i => !(Fin.tail q i))) := by
      intro J
      simp only [maskTerm, pairTerm]
      rw [selected_succ, selected_succ (q := fun i => !(q i)), tail_not]
      simp only [hq0, Fin.cons_zero, Fin.tail_cons, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
    rw [Finset.sum_congr rfl fun J _ => hterm J,
      sum_selected_eq (sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n)))) k (Fin.tail q)
        (pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u) _ _ rfl rfl,
      hcnt]
    have hβ : k + 2 - (1 + maskCount (Fin.tail q)) = maskCount (fun i => !(Fin.tail q i)) + 1 := by
      omega
    rw [hβ, add_comm 1]
    refine sum_sq_pairTerm_ofFn_le ν hc hA hApos _ (fun v => ?_) u
    simpa using h100 (maskCount (fun i => !(Fin.tail q i)) + 1) (by omega) (by omega) v
  calc
    Real.sqrt
          (∑ J : Fin k → Fin n,
            (∑ q ∈ middleMasks k,
                maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n)))
                  (Fin.cons u fun i =>
                      sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
                    Fin (k + 1) → EuclideanSpace ℝ (Fin n))
                  q) ^
              2) ≤
        ∑ q ∈ middleMasks k,
          Real.sqrt
            (∑ J : Fin k → Fin n,
              maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n)))
                  (Fin.cons u fun i =>
                      sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
                    Fin (k + 1) → EuclideanSpace ℝ (Fin n))
                  q ^
                2) :=
      sqrt_sum_sq_sum_le (middleMasks k) _
    _ ≤
        ∑ q ∈ middleMasks k,
          Real.sqrt
            (b (k + 2 - maskCount q) *
              cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (maskCount q) u) :=
      Finset.sum_le_sum fun q hq => Real.sqrt_le_sqrt (hmask q hq)
    _ =
        ∑ a ∈ Finset.Icc 2 (k - 1),
          ∑ q ∈ (middleMasks k).filter (fun q => maskCount q = a),
            Real.sqrt
              (b (k + 2 - a) * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) :=
      (Finset.sum_fiberwise_of_maps_to' hmaps
          (fun a =>
            Real.sqrt
              (b (k + 2 - a) *
                cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u))).symm
    _ =
        ∑ a ∈ Finset.Icc 2 (k - 1),
          (k.choose (a - 1) : ℝ) *
            Real.sqrt
              (b (k + 2 - a) * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.sum_const, nsmul_eq_mul, hcard a ha]

end Algebra

/--
**Section 6 pointwise bound** (BKL (99)–(102) and the pointwise triangle inequality behind (104)):
for a compactly supported law with positive invertible covariance `A`, if the lower cumulants
satisfy
(100), `Σ_J κ_r(v, σ e_J)² ≤ b_r ⟪A v, v⟫` for `2 ≤ r < m`, then
`|L_m(u)|_A ≤ Σ_{a=2}^{m−2} C(m−1, a−1) √(b_{m−a+1} E_{a+1})`, with `|L_m(u)|²_A = Σ_J L_m(u, σ
e_J)²`. -/
theorem sqrt_lowerDrift_energy_le (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos :
      ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    {m : ℕ} (hm : 3 ≤ m) (b : ℕ → ℝ) (hb : ∀ r, 0 ≤ b r)
    (h100 :
      ∀ r,
        2 ≤ r →
          r < m →
            ∀ v : EuclideanSpace ℝ (Fin n),
              cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r - 1) v ≤
                b r * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt
        (∑ J : Fin (m - 1) → Fin n,
          lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n)))
              (Fin.cons u fun k =>
                  inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                    (EuclideanSpace.basisFun (Fin n) ℝ (J k)) :
                Fin (m - 1 + 1) → EuclideanSpace ℝ (Fin n))
              0 ^
            2) ≤
      ∑ a ∈ Finset.Icc 2 (m - 2),
        ((m - 1).choose (a - 1) : ℝ) *
          Real.sqrt
            (b (m - a + 1) * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) := by
  have _ := hb 0
  have h :=
    sqrt_sum_lowerDrift_sq_le_aux ν hc hA hApos (m - 1) b
      (fun r hr hrm v => h100 r hr (by omega) v) u
  have hI : m - 1 - 1 = m - 2 := by omega
  rw [hI] at h
  refine h.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_Icc] at ha
  have hβ : m - 1 + 2 - a = m - a + 1 := by omega
  rw [hβ]

end FunctionalInequalities.KLS.BKL

end PointwiseCumulantEnergy
