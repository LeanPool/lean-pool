/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.KohnSham.Existence
import TauCeti.Analysis.Convex.PermutationOrbit
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.NormNum
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Ring

/-!
# Interior densities are strictly positive mixtures of configurations

* `hypersimplex_mixture`: every `ρ ∈ [0,1]^M` with `Σ_i ρ_i = N` is a mixture of `N`-particle
  configuration densities, by applying Rado’s theorem to a vector of zeros and ones.
* `interior_positive_mixture`: if moreover `0 < ρ_i < 1`, the mixture can be chosen with all weights
  positive.
* `ks_potential_exists_interior`: every density with `0 < ρ_i < 1`, `Σ_i ρ_i = N` is the density of
  a ground-state ensemble of a (non-)interacting lattice Hamiltonian — the textbook form of
  Kohn–Sham existence.
-/

@[expose] public section

namespace DFT

variable {M N : ℕ}

/-- `ρ` is a mixture of configuration densities. -/
def IsMixture (ρ : Fin M → ℝ) (μ : Conf M N → ℝ) : Prop :=
  μ ∈ probVec (Conf M N) ∧ ρ = fun i => ∑ s, μ s * occF i s

lemma mixture_combo {ρ1 ρ2 : Fin M → ℝ} {μ1 μ2 : Conf M N → ℝ} (h1 : IsMixture ρ1 μ1)
    (h2 : IsMixture ρ2 μ2)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    IsMixture (fun i => θ * ρ1 i + (1 - θ) * ρ2 i) (fun s => θ * μ1 s + (1 - θ) * μ2 s) := by
  obtain ⟨⟨p1, s1⟩, e1⟩ := h1; obtain ⟨⟨p2, s2⟩, e2⟩ := h2
  refine ⟨⟨fun s => by nlinarith [p1 s, p2 s], ?_⟩, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, s1, s2]; ring
  · subst e1 e2; funext i
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

/-- The hypersimplex is the convex hull of the fixed-particle occupation vectors. -/
theorem hypersimplex_mixture {ρ : Fin M → ℝ} (hbox : ∀ i, 0 ≤ ρ i ∧ ρ i ≤ 1)
    (hsum : ∑ i, ρ i = N) : ∃ μ : Conf M N → ℝ, IsMixture ρ μ := by
  classical
  have hfill : N ≤ M := by
    have h : (N : ℝ) ≤ ∑ _ : Fin M, (1 : ℝ) := hsum ▸ Finset.sum_le_sum fun i _ => (hbox i).2
    exact_mod_cast (show (N : ℝ) ≤ M by simpa using h)
  let base : Conf M N := ⟨Finset.univ.map (Fin.castLEEmb hfill), by simp⟩
  let w : Fin M → ℝ := fun i => occF i base
  have w_eq (i : Fin M) : w i = if (i : ℕ) < N then 1 else 0 := by
    have hm : i ∈ base.1 ↔ (i : ℕ) < N := by
      simp only [base, Finset.mem_map, Finset.mem_univ, true_and, Fin.castLEEmb_apply]
      exact ⟨fun ⟨j, hj⟩ => hj ▸ j.isLt, fun hi => ⟨⟨i, hi⟩, rfl⟩⟩
    simp only [w, occF, hm]
  have hw : Antitone w := by
    intro i j hij
    change (i : ℕ) ≤ (j : ℕ) at hij
    rw [w_eq, w_eq]
    split_ifs <;> norm_num
    omega
  let sorted := ρ ∘ Tuple.sortDesc ρ
  have htotal : ∑ i, sorted i = ∑ i, w i := by
    simpa only [sorted, Function.comp_apply, Equiv.sum_comp, w, sum_occF] using hsum
  have horbit := (TauCeti.mem_convexHull_range_comp_perm_iff hw).2
    ⟨fun k => ?_, by simpa only [sorted, Function.comp_apply, Equiv.sum_comp] using htotal⟩
  · have himage : Set.range (fun σ : Equiv.Perm (Fin M) => w ∘ σ) ⊆
        (↑(Finset.univ.image (fun s : Conf M N => fun i => occF i s)) : Set (Fin M → ℝ)) := by
      rintro _ ⟨σ, rfl⟩
      let s : Conf M N := ⟨base.1.map σ.symm.toEmbedding, by rw [Finset.card_map, base.2]⟩
      refine Finset.mem_image.mpr ⟨s, Finset.mem_univ _, ?_⟩
      funext i
      simp only [Function.comp_apply, w, occF, s, Finset.mem_map, Equiv.toEmbedding_apply,
        Equiv.symm_apply_eq]
      simp
    have hinjective : Function.Injective fun s : Conf M N => fun i => occF i s := by
      intro a b hab
      apply Subtype.ext
      ext i
      have h := congrFun hab i
      by_cases ha : i ∈ a.1 <;> by_cases hb : i ∈ b.1 <;> simp_all [occF]
    obtain ⟨μ, hn, ht, he⟩ := Finset.mem_convexHull'.mp (convexHull_mono himage horbit)
    have hinjOn : Set.InjOn (fun s : Conf M N => fun i => occF i s)
        (↑(Finset.univ : Finset (Conf M N)) : Set (Conf M N)) := hinjective.injOn
    rw [Finset.sum_image hinjOn] at ht he
    refine ⟨fun s => μ (fun i => occF i s),
      ⟨fun s => hn _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)), ht⟩, funext fun i => ?_⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (congrFun he i).symm
  · by_cases hk : k ≤ N
    · rw [TauCeti.prefixSum_def, TauCeti.prefixSum_def]
      exact Finset.sum_le_sum fun i hi => by
        rw [w_eq, ite_eq_left ((Finset.mem_filter.mp hi).2.trans_le hk)]
        exact (hbox (Tuple.sortDesc ρ i)).2
    · exact TauCeti.prefixSum_le_of_sum_le htotal.le fun i hi => by
        rw [w_eq, ite_eq_right (by omega)]
        exact (hbox (Tuple.sortDesc ρ i)).1

/-- **Interior densities are strictly positive mixtures.** -/
theorem interior_positive_mixture [Nonempty (Conf M N)] {ρ : Fin M → ℝ}
    (hρ : ∀ i, 0 < ρ i ∧ ρ i < 1)
    (hsum : ∑ i, ρ i = N) :
    ∃ lam : Conf M N → ℝ, (∀ s, 0 < lam s) ∧ ∑ s, lam s = 1 ∧
        ρ = fun i => ∑ s, lam s * occF i s := by
  classical
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, ((Finset.univ : Finset (Conf M N)).card : ℝ) = L := ⟨_, rfl⟩
  have hL : 0 < L := by
    rw [← hLdef]; exact_mod_cast Finset.card_pos.mpr Finset.univ_nonempty
  set ρbar : Fin M → ℝ := fun i => ∑ s : Conf M N, (1 / L) * occF i s
  have hbar : ∀ i, 0 ≤ ρbar i ∧ ρbar i ≤ 1 := by
    intro i
    constructor
    · exact Finset.sum_nonneg fun s _ => mul_nonneg (by positivity)
        (by unfold occF; split_ifs <;> norm_num)
    · calc ρbar i ≤ ∑ s : Conf M N, (1 / L) * 1 :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
                (by unfold occF; split_ifs <;> norm_num)
              (by positivity)
        _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul, hLdef]; field_simp
  have hbarsum : ∑ i, ρbar i = N := by
    simp only [ρbar]; rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_occF, Finset.sum_const, nsmul_eq_mul, hLdef]; field_simp
  -- choose ε
  by_cases hM : (Finset.univ : Finset (Fin M)).Nonempty
  · set ε := Finset.univ.inf' hM fun i => min (ρ i) (1 - ρ i)
    have hε : 0 < ε := by
      rw [Finset.lt_inf'_iff]; intro i _; exact lt_min (hρ i).1 (by linarith [(hρ i).2])
    have hεle : ∀ i, ε ≤ min (ρ i) (1 - ρ i) := fun i => Finset.inf'_le _ (Finset.mem_univ i)
    obtain ⟨i0⟩ := hM
    have hε1 : ε < 1 := by
      have := hεle i0; have := min_le_left (ρ i0) (1 - ρ i0); linarith [(hρ i0).2]
    set ρ' : Fin M → ℝ := fun i => (ρ i - ε * ρbar i) / (1 - ε)
    have hbox' : ∀ i, 0 ≤ ρ' i ∧ ρ' i ≤ 1 := by
      intro i
      have h1 := hεle i
      have hm1 := min_le_left (ρ i) (1 - ρ i)
      have hm2 := min_le_right (ρ i) (1 - ρ i)
      have hpos : 0 < 1 - ε := by linarith
      constructor
      · apply div_nonneg _ hpos.le; nlinarith [(hbar i).2, (hbar i).1]
      · rw [div_le_one hpos]; nlinarith [(hbar i).1, (hbar i).2]
    have hsum' : ∑ i, ρ' i = N := by
      simp only [ρ', ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, hbarsum]
      have : (1 - ε) ≠ 0 := by linarith
      field_simp
    obtain ⟨μ, ⟨hμ0, hμ1⟩, hμρ⟩ := hypersimplex_mixture hbox' hsum'
    refine ⟨fun s => (1 - ε) * μ s + ε / L, fun s => by nlinarith [hμ0 s, div_pos hε hL], ?_, ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, Finset.sum_const, nsmul_eq_mul, hLdef];
        field_simp; ring
    · funext i
      have hρi : ρ i = (1 - ε) * ρ' i + ε * ρbar i := by
        simp only [ρ']; have : (1 - ε) ≠ 0 := by linarith
        field_simp; ring
      rw [hρi, hμρ]
      simp only [ρbar, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      congr 1; apply Finset.sum_congr rfl; intro s _; ring
  · -- no sites: the uniform weights work trivially
    refine ⟨fun _ => 1 / L, fun _ => by positivity, ?_, ?_⟩
    · rw [Finset.sum_const, nsmul_eq_mul, hLdef]; field_simp
    · funext i; exact absurd ⟨i, Finset.mem_univ i⟩ hM

/-- **v-representability of interior densities.** For `N` spinless fermions (`0 < N < M`) on any
graph, with any hopping `t` and any configuration-diagonal interaction, every density with
`0 < ρ_i < 1` and `Σ_i ρ_i = N` is the density of a ground-state ensemble of `H(v)` for some
potential `v`. -/
theorem v_representable_interior [Nonempty (Conf M N)] (G : SimpleGraph (Fin M))
    [DecidableRel G.Adj] (t : ℝ)
    (Vint : Conf M N → ℝ) (hN0 : 0 < N) (hNM : N < M) {ρ : Fin M → ℝ} (hρ : ∀ i, 0 < ρ i ∧ ρ i < 1)
    (hsum : ∑ i, ρ i = N) :
    ∃ v : Fin M → ℝ, ∃ Γ ∈ Ens (H0F G t Vint) occF v, ensDens occF Γ = ρ := by
  obtain ⟨lam, hlam, hl1, hlρ⟩ := interior_positive_mixture hρ hsum
  exact v_representable_lattice_fermions G t Vint hN0 hNM hlam hl1 hlρ

/-- **Existence of Kohn–Sham potentials (textbook form).** Every density with `0 < ρ_i < 1`,
`Σ_i ρ_i = N` is the ground-state ensemble density of a non-interacting system in some potential
`vs`. -/
theorem ks_potential_exists_interior [Nonempty (Conf M N)] (G : SimpleGraph (Fin M))
    [DecidableRel G.Adj] (t : ℝ)
    (hN0 : 0 < N) (hNM : N < M) {ρ : Fin M → ℝ} (hρ : ∀ i, 0 < ρ i ∧ ρ i < 1)
        (hsum : ∑ i, ρ i = N) :
    ∃ vs : Fin M → ℝ, ∃ Γ ∈ Ens (H0F G t (0 : Conf M N → ℝ)) occF vs, ensDens occF Γ = ρ :=
  v_representable_interior G t 0 hN0 hNM hρ hsum

end DFT
