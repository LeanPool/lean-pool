/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.GenericHK

/-!
# Orbital sign changes: hopping signs up to gauge

Changing the sign of the orbital at site `i` (`cᵢ ↦ -cᵢ`) reverses the hopping on every bond at
`i` and leaves the potential, the interaction and the densities unchanged. For `N` fermions it acts
on configurations by the diagonal sign matrix `D = diag(ε)`, `ε(c) = ∏_{i ∈ c} σ_i`; the fermionic
ordering signs of `Γ` are unaffected (`gamma_signConj`). Hence the generic Hohenberg–Kohn theorem
holds for every hopping pattern that orbital sign changes bring to a common sign
(`generic_hk_lattice_fermions_gauge`). The gauge change itself is standard; the graph-theoretic
criterion for which sign patterns qualify (balance of signed graphs, Harary) is not formalized
here, except for the triangle and the 4-cycle.

* `signConj ε H`: conjugation by `diag ε` (`ε c = ±1`), with `signConj_apply`, `signConj_add`,
  `signConj_neg`, `signConj_diagonal`; `hamN_signConj`, `qf_signConj`, `dot_gauge`, `gauge_gauge`,
  `gauge_ne_zero`, `isGroundState_signConj`, `dens_signConj`, `nonUV_signConj`.
* `confSign`, `gaugeHop`, `confSign_mul_self`, `gaugeHop_gaugeHop`, `gamma_signConj`,
  `hopM_gaugeHop`, `H0Fw_gaugeHop`, `nonUV_H0Fw_gaugeHop`.
* `generic_hk_lattice_fermions_gauge`, `triangle_common_sign`, `cycle4_no_common_sign`.
-/

@[expose] public section

namespace DFT

open Matrix

section signConj

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- Conjugation by the diagonal sign matrix `diag ε`: `(D H D) i j = ε i ε j H i j`. -/
def signConj (ε : C → ℝ) (H : Matrix C C ℝ) : Matrix C C ℝ :=
  Matrix.of fun i j => ε i * ε j * H i j

omit [Fintype C] [DecidableEq C] in
lemma signConj_apply (ε : C → ℝ) (H : Matrix C C ℝ) (i j : C) :
    signConj ε H i j = ε i * ε j * H i j := rfl

omit [Fintype C] [DecidableEq C] in
lemma signConj_add (ε : C → ℝ) (A B : Matrix C C ℝ) :
    signConj ε (A + B) = signConj ε A + signConj ε B := by
  ext i j; simp [signConj_apply]; ring

omit [Fintype C] [DecidableEq C] in
lemma signConj_neg (ε : C → ℝ) (A : Matrix C C ℝ) : signConj ε (-A) = -signConj ε A := by
  ext i j; simp [signConj_apply]

omit [Fintype C] in
lemma signConj_diagonal {ε : C → ℝ} (hε : ∀ c, ε c * ε c = 1) (d : C → ℝ) :
    signConj ε (diagonal d) = diagonal d := by
  ext i j
  by_cases h : i = j
  · subst h; simp [signConj_apply, hε]
  · simp [signConj_apply, h]

omit [Fintype C] in
/-- The potential term is diagonal, so it commutes with the gauge. -/
lemma hamN_signConj {ε : C → ℝ} (hε : ∀ c, ε c * ε c = 1) (H0 : Matrix C C ℝ) (n : V → C → ℝ)
    (v : V → ℝ) : hamN (signConj ε H0) n v = signConj ε (hamN H0 n v) := by
  unfold hamN
  rw [signConj_add, signConj_diagonal hε]

omit [DecidableEq C] in
lemma qf_signConj (ε : C → ℝ) (H : Matrix C C ℝ) (ψ : C → ℝ) :
    qf (signConj ε H) ψ = qf H (fun c => ε c * ψ c) := by
  simp only [qf, dotProduct, mulVec, signConj_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq C] in
/-- The gauge preserves the norm. -/
lemma dot_gauge {ε : C → ℝ} (hε : ∀ c, ε c * ε c = 1) (ψ : C → ℝ) :
    (fun c => ε c * ψ c) ⬝ᵥ (fun c => ε c * ψ c) = ψ ⬝ᵥ ψ := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  linear_combination (ψ c * ψ c) * hε c

omit [Fintype C] [DecidableEq C] in
/-- The gauge is an involution. -/
lemma gauge_gauge {ε : C → ℝ} (hε : ∀ c, ε c * ε c = 1) (ψ : C → ℝ) :
    (fun c => ε c * (ε c * ψ c)) = ψ := by
  funext c; linear_combination ψ c * hε c

omit [Fintype C] [DecidableEq C] in
/-- The gauge preserves nonzero vectors. -/
lemma gauge_ne_zero {ε : C → ℝ} (hε : ∀ c, ε c * ε c = 1) {ψ : C → ℝ} :
    (fun c => ε c * ψ c) ≠ 0 ↔ ψ ≠ 0 := by
  constructor
  · rintro h rfl; exact h (by funext c; simp)
  · intro h h0
    apply h
    rw [← gauge_gauge hε ψ]
    funext c
    have := congrFun h0 c
    simp only [Pi.zero_apply] at this ⊢
    rw [this, mul_zero]

omit [DecidableEq C] in
/-- `ψ` is a ground state of `D H D` iff `D ψ` is a ground state of `H`. -/
lemma isGroundState_signConj {ε : C → ℝ} (hε : ∀ c, ε c * ε c = 1) (H : Matrix C C ℝ)
    (ψ : C → ℝ) : IsGroundState (signConj ε H) ψ ↔ IsGroundState H (fun c => ε c * ψ c) := by
  constructor
  · rintro ⟨hψ, hmin⟩
    refine ⟨(gauge_ne_zero hε).mpr hψ, fun φ => ?_⟩
    have h := hmin (fun c => ε c * φ c)
    rw [qf_signConj, qf_signConj, gauge_gauge hε, dot_gauge hε] at h
    rw [dot_gauge hε]
    exact h
  · rintro ⟨hψ, hmin⟩
    refine ⟨(gauge_ne_zero hε).mp hψ, fun φ => ?_⟩
    have h := hmin (fun c => ε c * φ c)
    rw [dot_gauge hε, dot_gauge hε] at h
    rw [qf_signConj, qf_signConj]
    exact h

omit [DecidableEq C] [Fintype V] in
/-- The density does not see the gauge. -/
lemma dens_signConj {ε : C → ℝ} (hε : ∀ c, ε c * ε c = 1) (n : V → C → ℝ) (ψ : C → ℝ) :
    dens n (fun c => ε c * ψ c) = dens n ψ := by
  funext i
  simp only [dens]
  refine Finset.sum_congr rfl fun c _ => ?_
  linear_combination (n i c * ψ c ^ 2) * hε c

/-- The exceptional (non-uniquely v-representable) potentials are the same for `H0` and `D H0 D`. -/
lemma nonUV_signConj {ε : C → ℝ} (hε : ∀ c, ε c * ε c = 1) (H0 : Matrix C C ℝ) (n : V → C → ℝ)
    (v : V → ℝ) : NonUV (signConj ε H0) n v ↔ NonUV H0 n v := by
  constructor
  · rintro ⟨ψ, v', h1, h2, hne⟩
    rw [hamN_signConj hε, isGroundState_signConj hε] at h1 h2
    exact ⟨_, v', h1, h2, hne⟩
  · rintro ⟨ψ, v', h1, h2, hne⟩
    refine ⟨fun c => ε c * ψ c, v', ?_, ?_, hne⟩
    · rw [hamN_signConj hε, isGroundState_signConj hε, gauge_gauge hε]; exact h1
    · rw [hamN_signConj hε, isGroundState_signConj hε, gauge_gauge hε]; exact h2

end signConj

section fermions

variable {M N : ℕ}

/-- The many-body sign `ε(c) = ∏_{i ∈ c} σ_i` of a configuration. -/
def confSign (σ : Fin M → ℝ) (s : Conf M N) : ℝ := ∏ k, σ (τs s k)

/-- Hopping after the orbital sign changes `σ`: `σ_a σ_b t_ab`. -/
def gaugeHop (σ : Fin M → ℝ) (t : Fin M → Fin M → ℝ) : Fin M → Fin M → ℝ :=
  fun a b => σ a * σ b * t a b

lemma confSign_mul_self {σ : Fin M → ℝ} (hσ : ∀ i, σ i * σ i = 1) (s : Conf M N) :
    confSign σ s * confSign σ s = 1 := by
  unfold confSign
  rw [← Finset.prod_mul_distrib]
  simp [hσ]

lemma gaugeHop_gaugeHop {σ : Fin M → ℝ} (hσ : ∀ i, σ i * σ i = 1) (t : Fin M → Fin M → ℝ) :
    gaugeHop σ (gaugeHop σ t) = t := by
  funext a b
  simp only [gaugeHop]
  linear_combination (σ b * σ b * t a b) * hσ a + t a b * hσ b

/-- **Gauge covariance of `Γ`.** Conjugating the one-body matrix by `diag σ` (`σ_i = ±1`)
conjugates the many-body matrix by `diag ε`, `ε(c) = ∏_{i ∈ c} σ_i`: the fermionic ordering signs
are not affected. -/
theorem gamma_signConj {σ : Fin M → ℝ} (hσ : ∀ i, σ i * σ i = 1) (h : Matrix (Fin M) (Fin M) ℝ) :
    (Γ (signConj σ h) : Matrix (Conf M N) (Conf M N) ℝ) = signConj (confSign σ) (Γ h) := by
  ext s s'
  rw [signConj_apply, gamma_leibniz, gamma_leibniz]
  have key : ∀ (π : Equiv.Perm (Fin N)) (j0 : Fin N),
      signConj σ h (τs s (π j0)) (τs s' j0) *
          ∏ j, (if j = j0 then 1 else (if τs s (π j) = τs s' j then (1 : ℝ) else 0)) =
        confSign σ s * confSign σ s' * (h (τs s (π j0)) (τs s' j0) *
          ∏ j, (if j = j0 then 1 else (if τs s (π j) = τs s' j then (1 : ℝ) else 0))) := by
    intro π j0
    by_cases hP : ∏ j, (if j = j0 then 1 else (if τs s (π j) = τs s' j then (1 : ℝ) else 0)) = 0
    · rw [hP]; ring
    · have hj : ∀ j, j ≠ j0 → τs s (π j) = τs s' j := by
        intro j hj
        by_contra hne
        exact hP (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj, hne]))
      have e : ∏ k, σ (τs s k) = ∏ j, σ (τs s (π j)) :=
        (Equiv.prod_comp π (fun k => σ (τs s k))).symm
      have hε : confSign σ s * confSign σ s' = σ (τs s (π j0)) * σ (τs s' j0) := by
        unfold confSign
        rw [e, ← Finset.prod_mul_distrib, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j0)]
        rw [Finset.prod_eq_one (fun j hj' => by rw [hj j (Finset.ne_of_mem_erase hj'), hσ])]
        ring
      rw [signConj_apply, hε]
      ring
  simp_rw [key]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j0 _ => ?_
  ring

lemma hopM_gaugeHop (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (σ : Fin M → ℝ)
    (t : Fin M → Fin M → ℝ) : hopM G (gaugeHop σ t) = signConj σ (hopM G t) := by
  ext a b
  simp only [hopM, gaugeHop, signConj_apply]
  split_ifs <;> simp

/-- **The many-body Hamiltonian under orbital sign changes**: `H0(σσt) = D H0(t) D`. -/
theorem H0Fw_gaugeHop (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] {σ : Fin M → ℝ}
    (hσ : ∀ i, σ i * σ i = 1) (t : Fin M → Fin M → ℝ) (Vint : Conf M N → ℝ) :
    H0Fw G (gaugeHop σ t) Vint = signConj (confSign σ) (H0Fw G t Vint) := by
  unfold H0Fw
  rw [hopM_gaugeHop, ← signConj_neg, gamma_signConj hσ, signConj_add,
    signConj_diagonal (confSign_mul_self hσ)]

/-- **The exceptional potentials are gauge invariant**: the hoppings `t` and `σ_a σ_b t_ab` have
the same exceptional potentials. -/
theorem nonUV_H0Fw_gaugeHop (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] {σ : Fin M → ℝ}
    (hσ : ∀ i, σ i * σ i = 1) (t : Fin M → Fin M → ℝ) (Vint : Conf M N → ℝ) (v : Fin M → ℝ) :
    NonUV (H0Fw G (gaugeHop σ t) Vint) occF v ↔ NonUV (H0Fw G t Vint) occF v := by
  rw [H0Fw_gaugeHop G hσ, nonUV_signConj (confSign_mul_self hσ)]

/-- **Generic Hohenberg–Kohn theorem up to orbital sign changes.** On a connected graph with
symmetric hopping, `0 < N < M` and any configuration-diagonal interaction: if signs `σ_i = ±1` and
`s` exist with `s σ_a σ_b t_ab > 0` on every bond, the potentials with a non-uniquely
v-representable ground state lie in a closed, nowhere dense, null set. -/
theorem generic_hk_lattice_fermions_gauge {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a)
    {σ : Fin M → ℝ} (hσ : ∀ i, σ i * σ i = 1) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * (σ a * σ b * t a b))
    (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0Fw G t Vint) occF v} ⊆ Z := by
  have hsym : ∀ a b, gaugeHop σ t a b = gaugeHop σ t b a := by
    intro a b; simp only [gaugeHop]; rw [htsym a b]; ring
  obtain ⟨Z, h1, h2, h3, h4⟩ :=
    generic_hk_lattice_fermions_w (t := gaugeHop σ t) hG hsym (s := s) hts hN0 hNM Vint
  refine ⟨Z, h1, h2, h3, fun v hv => h4 ?_⟩
  exact (nonUV_H0Fw_gaugeHop G hσ t Vint v).mpr hv

/-- The sign of `t_ab t_bc t_cd t_da` around a 4-cycle is gauge invariant: if it is negative, no
orbital signs `σ` (`σ_i = ±1`) and overall sign `s` make all four `s σ σ t` positive. (The square
with one negative bond is not gauge-equivalent to a common sign.) -/
theorem cycle4_no_common_sign {σ : Fin M → ℝ} (hσ : ∀ i, σ i * σ i = 1) (s : ℝ)
    (t : Fin M → Fin M → ℝ) (a b c d : Fin M) (hneg : t a b * t b c * t c d * t d a < 0) :
    ¬ (0 < s * (σ a * σ b * t a b) ∧ 0 < s * (σ b * σ c * t b c) ∧ 0 < s * (σ c * σ d * t c d) ∧
        0 < s * (σ d * σ a * t d a)) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hprod := mul_pos (mul_pos (mul_pos h1 h2) h3) h4
  have e : s * (σ a * σ b * t a b) * (s * (σ b * σ c * t b c)) * (s * (σ c * σ d * t c d)) *
      (s * (σ d * σ a * t d a)) = (s * s) * (s * s) * (t a b * t b c * t c d * t d a) := by
    linear_combination (s * s * (s * s) * (t a b * t b c * t c d * t d a)) *
      ((σ b * σ b) * (σ c * σ c) * (σ d * σ d) * hσ a + (σ c * σ c) * (σ d * σ d) * hσ b +
        (σ d * σ d) * hσ c + hσ d)
  rw [e] at hprod
  have hs : 0 ≤ (s * s) * (s * s) := mul_nonneg (mul_self_nonneg s) (mul_self_nonneg s)
  nlinarith

/-- Closes the two goals of `triangle_common_sign` for an explicit witness. -/
local macro "triangle_gauge_tac" : tactic =>
  `(tactic| first
    | (intro a b hab; fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> linarith; done)
    | (intro i; fin_cases i <;> norm_num; done))

/-- Every sign pattern on the triangle is gauge-equivalent to a common sign: for nonzero symmetric
hopping on the triangle there are orbital signs `σ` (`σ_i = ±1`) and an overall sign `s` with
`s σ_a σ_b t_ab > 0` on every bond (`σ_a σ_b t_ab` all positive, `s = 1`, if `t₀₁ t₀₂ t₁₂ > 0`;
all negative, `s = −1`, otherwise). -/
theorem triangle_common_sign {t : Fin 3 → Fin 3 → ℝ} (htsym : ∀ a b, t a b = t b a)
    (h01 : t 0 1 ≠ 0) (h02 : t 0 2 ≠ 0) (h12 : t 1 2 ≠ 0) :
    ∃ σ : Fin 3 → ℝ, ∃ s : ℝ, (∀ i, σ i * σ i = 1) ∧
      ∀ a b, (⊤ : SimpleGraph (Fin 3)).Adj a b → 0 < s * (σ a * σ b * t a b) := by
  have e10 := htsym 1 0
  have e20 := htsym 2 0
  have e21 := htsym 2 1
  rcases lt_or_gt_of_ne h01 with x | x <;> rcases lt_or_gt_of_ne h02 with y | y <;>
    rcases lt_or_gt_of_ne h12 with z | z
  · refine ⟨![1, 1, 1], -1, ?_, ?_⟩ <;> triangle_gauge_tac
  · refine ⟨![1, -1, -1], 1, ?_, ?_⟩ <;> triangle_gauge_tac
  · refine ⟨![1, -1, 1], 1, ?_, ?_⟩ <;> triangle_gauge_tac
  · refine ⟨![1, 1, -1], -1, ?_, ?_⟩ <;> triangle_gauge_tac
  · refine ⟨![1, 1, -1], 1, ?_, ?_⟩ <;> triangle_gauge_tac
  · refine ⟨![1, -1, 1], -1, ?_, ?_⟩ <;> triangle_gauge_tac
  · refine ⟨![1, -1, -1], -1, ?_, ?_⟩ <;> triangle_gauge_tac
  · refine ⟨![1, 1, 1], 1, ?_, ?_⟩ <;> triangle_gauge_tac

end fermions

end DFT
