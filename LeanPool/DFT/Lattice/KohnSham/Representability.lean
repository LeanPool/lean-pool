/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.KohnSham.Maximizer
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Instances.Matrix

/-!
# Ensemble v-representability

* `exists_gs_below`: at a maximiser `v*` of `E(v) − v·ρ`, for every direction `w` some normalised
  ground state of `H(v*)` has `w·ρ_ψ ≤ w·ρ` (limit of ground states along `v* + t w`, `t → 0⁺`).
* `Ens H0 n v`: ground-state ensembles (density matrices supported on the ground-state space of
  `H(v)`), and their densities `ensDens`. The ensemble densities form a compact convex set.
* `ensemble_v_representable`: every strictly positive mixture of configuration densities is the
  density of a ground-state ensemble of some `H(v)`. With `H0` non-interacting this is the existence
  of a Kohn–Sham potential.
-/

@[expose] public section

namespace DFT

open Matrix Filter Topology

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V] [Nonempty C]

omit [DecidableEq V] [Nonempty C] in
lemma qf_hamN_add (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v w : V → ℝ) (t : ℝ) (ψ : C → ℝ) :
    qf (hamN H0 n (v + t • w)) ψ = qf (hamN H0 n v) ψ + t * (w ⬝ᵥ dens n ψ) := by
  rw [qf_hamN, qf_hamN]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, dotProduct,
    Finset.mul_sum]
  ring_nf

omit [DecidableEq C] [Nonempty C] in
lemma continuous_qf (H : Matrix C C ℝ) : Continuous fun ψ : C → ℝ => qf H ψ := by
  unfold qf dotProduct mulVec dotProduct; fun_prop

omit [DecidableEq C] [DecidableEq V] [Nonempty C] in
lemma continuous_dens (n : V → C → ℝ) (w : V → ℝ) : Continuous fun ψ : C → ℝ => w ⬝ᵥ dens n ψ := by
  unfold dotProduct dens; fun_prop

omit [DecidableEq C] [Nonempty C] in
lemma isCompact_sphere1 : IsCompact {ψ : C → ℝ | ψ ⬝ᵥ ψ = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by unfold dotProduct; fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : C → ℝ)) (r := 1)).subset fun ψ hψ => ?_
    simp only [Set.mem_ofPred_eq] at hψ
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro c
    rw [Real.norm_eq_abs, abs_le_one_iff_mul_self_le_one]
    rw [← hψ]
    exact Finset.single_le_sum (f := fun d => ψ d * ψ d) (fun d _ => mul_self_nonneg _)
        (Finset.mem_univ c)

section
variable {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} (hn0 : ∀ i c, 0 ≤ n i c) {Nr : ℝ}
  (hN : ∀ c, ∑ i, n i c = Nr)
include hH0 hn0 hN

omit [DecidableEq V] in
/-- **Ground states below the target density in every direction.** -/
theorem exists_gs_below {ρ vs : V → ℝ} (hmax : ∀ v, Egs H0 n v - v ⬝ᵥ ρ ≤ Egs H0 n vs - vs ⬝ᵥ ρ)
    (w : V → ℝ) : ∃ ψ, IsGroundState (hamN H0 n vs) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧ w ⬝ᵥ dens n ψ ≤ w ⬝ᵥ ρ := by
  set t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ht : ∀ k, 0 < t k := fun k => by positivity
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose ψ hψ hn using fun k => exists_groundState (hamN_isSymm hH0 n (vs + t k • w))
  -- (i) each ψ k lies below ρ in direction w
  have hbelow : ∀ k, w ⬝ᵥ dens n (ψ k) ≤ w ⬝ᵥ ρ := by
    intro k
    have h1 := hmax (vs + t k • w)
    have h2 := qf_groundState_eq (hamN_isSymm hH0 n (vs + t k • w)) (hψ k) (hn k)
    rw [qf_hamN_add] at h2
    have h3 := gsEnergy_le (hamN_isSymm hH0 n vs) (hn k)
    have hd : (vs + t k • w) ⬝ᵥ ρ = vs ⬝ᵥ ρ + t k * (w ⬝ᵥ ρ) := by
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
    unfold Egs at h1
    rw [hd] at h1
    have : t k * (w ⬝ᵥ dens n (ψ k)) ≤ t k * (w ⬝ᵥ ρ) := by linarith
    exact le_of_mul_le_mul_left this (ht k)
  -- (ii) a convergent subsequence
  obtain ⟨ψl, hψl, φ, hφ, hlim⟩ := isCompact_sphere1.tendsto_subseq (x := ψ) (fun k => hn k)
  have hnl : ψl ⬝ᵥ ψl = 1 := hψl
  have htφ : Tendsto (t ∘ φ) atTop (𝓝 0) := ht0.comp hφ.tendsto_atTop
  -- energies converge
  have hE : Tendsto (fun j => Egs H0 n (vs + t (φ j) • w)) atTop (𝓝 (Egs H0 n vs)) := by
    have hc := (continuous_Egs hH0 hn0 hN).tendsto vs
    have : Tendsto (fun j => vs + t (φ j) • w) atTop (𝓝 vs) := by
      have := (tendsto_const_nhds (x := vs)).add (htφ.smul_const w)
      simpa using this
    exact hc.comp this
  have hdlim : Tendsto (fun j => w ⬝ᵥ dens n (ψ (φ j))) atTop (𝓝 (w ⬝ᵥ dens n ψl)) :=
    ((continuous_dens n w).tendsto ψl).comp hlim
  have hqlim : Tendsto (fun j => qf (hamN H0 n vs) (ψ (φ j))) atTop (𝓝 (qf (hamN H0 n vs) ψl)) :=
    ((continuous_qf _).tendsto ψl).comp hlim
  have heq : ∀ j, qf (hamN H0 n vs) (ψ (φ j)) =
      Egs H0 n (vs + t (φ j) • w) - t (φ j) * (w ⬝ᵥ dens n (ψ (φ j))) := by
    intro j
    have h2 := qf_groundState_eq (hamN_isSymm hH0 n (vs + t (φ j) • w)) (hψ (φ j)) (hn (φ j))
    rw [qf_hamN_add] at h2
    unfold Egs; linarith
  have hqlim2 : Tendsto (fun j => qf (hamN H0 n vs) (ψ (φ j))) atTop
      (𝓝 (Egs H0 n vs - 0 * (w ⬝ᵥ dens n ψl))) := by
    simp_rw [heq]
    exact hE.sub (htφ.mul hdlim)
  have hql : qf (hamN H0 n vs) ψl = gsEnergy (hamN H0 n vs) := by
    have := tendsto_nhds_unique hqlim hqlim2
    rw [this]; simp [Egs]
  refine ⟨ψl, isGroundState_of_qf_eq (hamN_isSymm hH0 n vs) hnl hql, hnl, ?_⟩
  exact le_of_tendsto' hdlim (fun j => hbelow (φ j))

end

/-- Ground-state ensembles of `H(v)`: density matrices supported on the ground-state space. -/
def Ens (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : Set (Matrix C C ℝ) :=
  {Γ | Γᵀ = Γ ∧ (∀ x : C → ℝ, 0 ≤ x ⬝ᵥ (Γ *ᵥ x)) ∧ Γ.trace = 1 ∧ hamN H0 n v * Γ = Egs H0 n v • Γ}

/-- Density of an ensemble. -/
def ensDens (n : V → C → ℝ) (Γ : Matrix C C ℝ) : V → ℝ := fun i => ∑ c, n i c * Γ c c

omit [DecidableEq C] [Fintype V] [DecidableEq V] [Nonempty C] in
lemma ensDens_vecMulVec (n : V → C → ℝ) (ψ : C → ℝ) : ensDens n (vecMulVec ψ ψ) = dens n ψ := by
  funext i; simp [ensDens, dens, vecMulVec, sq]

omit [DecidableEq V] in
lemma pure_mem_Ens {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) {v : V → ℝ} {ψ : C → ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ) (hn : ψ ⬝ᵥ ψ = 1) : vecMulVec ψ ψ ∈ Ens H0 n v := by
  have heig : hamN H0 n v *ᵥ ψ = Egs H0 n v • ψ := by
    have := isGroundState_eigen (hamN_isSymm hH0 n v) hψ
    rw [hn, div_one, qf_groundState_eq (hamN_isSymm hH0 n v) hψ hn] at this
    exact this
  refine ⟨?_, fun x => ?_, ?_, ?_⟩
  · ext a b; simp [vecMulVec, mul_comm]
  · have : x ⬝ᵥ (vecMulVec ψ ψ *ᵥ x) = (ψ ⬝ᵥ x) * (ψ ⬝ᵥ x) := by
      simp only [vecMulVec, mulVec, dotProduct, of_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
    rw [this]; exact mul_self_nonneg _
  · simpa [Matrix.trace, vecMulVec, dotProduct] using hn
  · rw [mul_vecMulVec, heig]; ext a b; simp [vecMulVec, mul_assoc]

omit [Nonempty C] in
lemma quad_single (Γ : Matrix C C ℝ) (a b : C) (_hab : a ≠ b) (s : ℝ) :
    (Pi.single a 1 + s • Pi.single b 1 : C → ℝ) ⬝ᵥ (Γ *ᵥ (Pi.single a 1 + s • Pi.single b 1)) =
      Γ a a + s * (Γ a b + Γ b a) + s ^ 2 * Γ b b := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul,
    smul_eq_mul, mulVec_single_one, single_one_dotProduct]
  simp [Matrix.col]; ring

omit [DecidableEq V] in
lemma Ens_bound {H0 : Matrix C C ℝ} {n : V → C → ℝ} {v : V → ℝ} {Γ : Matrix C C ℝ}
    (hΓ : Γ ∈ Ens H0 n v) (a b : C) : Γ a b ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨hT, hP, htr, -⟩ := hΓ
  have hdiag : ∀ c, 0 ≤ Γ c c := fun c => by
    have := hP (Pi.single c 1); simpa [mulVec_single_one, single_one_dotProduct] using this
  have hdle : ∀ c d, c ≠ d → Γ c c + Γ d d ≤ 1 := by
    intro c d hcd
    rw [← htr, Matrix.trace, ← Finset.add_sum_erase _ _ (Finset.mem_univ c),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_univ d⟩)]
    simp only [diag_apply]
    have : 0 ≤ ∑ x ∈ (Finset.univ.erase c).erase d, Γ x x := Finset.sum_nonneg fun x _ => hdiag x
    linarith
  have hsym : Γ b a = Γ a b := by rw [← transpose_apply Γ a b, hT]
  by_cases hab : a = b
  · subst hab
    obtain ⟨c⟩ := (inferInstance : Nonempty C)
    have h1 : Γ a a ≤ 1 := by
      rw [← htr, Matrix.trace]
      exact Finset.single_le_sum (f := fun x => Γ x x) (fun x _ => hdiag x) (Finset.mem_univ a)
    exact ⟨by linarith [hdiag a], h1⟩
  · have hp := hP (Pi.single a 1 + (1 : ℝ) • Pi.single b 1)
    have hm := hP (Pi.single a 1 + (-1 : ℝ) • Pi.single b 1)
    rw [quad_single Γ a b hab] at hp hm
    rw [hsym] at hp hm
    have := hdle a b hab
    constructor <;> nlinarith [hdiag a, hdiag b]

omit [DecidableEq V] in
lemma convex_Ens (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : Convex ℝ (Ens H0 n v) := by
  rintro Γ1 ⟨h1T, h1P, h1t, h1H⟩ Γ2 ⟨h2T, h2P, h2t, h2H⟩ a b ha hb hab
  refine ⟨?_, fun x => ?_, ?_, ?_⟩
  · rw [transpose_add, transpose_smul, transpose_smul, h1T, h2T]
  · rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    nlinarith [h1P x, h2P x]
  · rw [trace_add, trace_smul, trace_smul, h1t, h2t, smul_eq_mul, smul_eq_mul]; linarith
  · rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, h1H, h2H, smul_comm a, smul_comm b,
      ← smul_add]

omit [DecidableEq V] in
lemma isCompact_Ens (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : IsCompact (Ens H0 n v) := by
  have hpi := isCompact_univ_pi (fun _ : C =>
    isCompact_univ_pi (fun _ : C => (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))))
  have hof : Continuous fun f : C → C → ℝ => (Matrix.of f : Matrix C C ℝ) :=
    continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)
  have hbox := hpi.image hof
  refine IsCompact.of_isClosed_subset hbox ?_ ?_
  · change IsClosed {Γ : Matrix C C ℝ | Γᵀ = Γ ∧ (∀ x : C → ℝ, 0 ≤ x ⬝ᵥ (Γ *ᵥ x)) ∧ Γ.trace = 1 ∧
      hamN H0 n v * Γ = Egs H0 n v • Γ}
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_eq continuous_id.matrix_transpose continuous_id) ?_
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun x => isClosed_le continuous_const
        (by
          unfold dotProduct
          exact continuous_finsetSum _ fun i _ => continuous_const.mul
            ((continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)))
    · exact IsClosed.inter (isClosed_eq continuous_id.matrix_trace continuous_const)
        (isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_const_smul _))
  · intro Γ hΓ
    refine ⟨fun i j => Γ i j, ?_, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    exact fun a b => Ens_bound hΓ a b

omit [DecidableEq C] [Fintype V] [DecidableEq V] [Nonempty C] in
lemma continuous_ensDens (n : V → C → ℝ) : Continuous (ensDens n) := by
  unfold ensDens
  exact continuous_pi fun i => continuous_finsetSum _ fun c _ =>
    continuous_const.mul (continuous_id.matrix_elem c c)

section
variable {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} (hn0 : ∀ i c, 0 ≤ n i c) {Nr : ℝ}
  (hN : ∀ c, ∑ i, n i c = Nr) {ρ : V → ℝ} {lam : C → ℝ} (hlam : ∀ c, 0 < lam c)
  (hsum : ∑ c, lam c = 1) (hρ : ρ = fun i => ∑ c, lam c * n i c) (hR : Rigid n)
include hH0 hn0 hN hlam hsum hρ hR

omit [DecidableEq V] in
/-- **Ensemble v-representability.** A strictly positive mixture of configuration densities is the
density of a ground-state ensemble of `H(v)` for some potential `v`. -/
theorem ensemble_v_representable : ∃ v : V → ℝ, ∃ Γ ∈ Ens H0 n v, ensDens n Γ = ρ := by
  classical
  obtain ⟨vs, hmax⟩ := exists_maximiser hH0 hn0 hN hlam hsum hρ hR
  refine ⟨vs, ?_⟩
  by_contra hno
  push Not at hno
  have hρt : ρ ∉ ensDens n '' Ens H0 n vs := fun ⟨Γ, hΓ, h⟩ => hno Γ hΓ h
  have hconv : Convex ℝ (ensDens n '' Ens H0 n vs) := by
    apply (convex_Ens H0 n vs).is_linear_image
    refine ⟨fun Γ1 Γ2 => ?_, fun a Γ => ?_⟩
    · funext i; simp [ensDens, mul_add, Finset.sum_add_distrib]
    · funext i
      simp only [ensDens, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.smul_apply]
      apply Finset.sum_congr rfl
      intro c _
      ring
  have hclosed : IsClosed (ensDens n '' Ens H0 n vs) :=
    ((isCompact_Ens H0 n vs).image (continuous_ensDens n)).isClosed
  obtain ⟨f, u, hfρ, hft⟩ := geometric_hahn_banach_point_closed hconv hclosed hρt
  set w : V → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hf : ∀ x, f x = w ⬝ᵥ x := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (V → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dotProduct]; apply Finset.sum_congr rfl; intro i _; ring
  obtain ⟨ψ, hψ, hn, hle⟩ := exists_gs_below hH0 hn0 hN hmax w
  have hin : dens n ψ ∈ ensDens n '' Ens H0 n vs :=
    ⟨vecMulVec ψ ψ, pure_mem_Ens hH0 n hψ hn, ensDens_vecMulVec n ψ⟩
  have h1 := hft _ hin
  rw [hf] at h1 hfρ
  linarith

end

end DFT
