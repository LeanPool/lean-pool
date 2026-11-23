/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.KohnSham.Existence

/-!
# Interior densities are strictly positive mixtures of configurations

* `hypersimplex_mixture`: every `ρ ∈ [0,1]^M` with `Σ_i ρ_i = N` is a mixture of `N`-particle
  configuration densities (vertex description of the hypersimplex; induction on the number of
  fractional sites).
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
  (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1 ∧ ρ = fun i => ∑ s, μ s * occF i s

/-- Number of fractional sites. -/
noncomputable def nfrac (ρ : Fin M → ℝ) : ℕ := (Finset.univ.filter fun i => 0 < ρ i ∧ ρ i < 1).card

lemma mixture_combo {ρ1 ρ2 : Fin M → ℝ} {μ1 μ2 : Conf M N → ℝ} (h1 : IsMixture ρ1 μ1)
    (h2 : IsMixture ρ2 μ2)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    IsMixture (fun i => θ * ρ1 i + (1 - θ) * ρ2 i) (fun s => θ * μ1 s + (1 - θ) * μ2 s) := by
  obtain ⟨p1, s1, e1⟩ := h1; obtain ⟨p2, s2, e2⟩ := h2
  refine ⟨fun s => by nlinarith [p1 s, p2 s], ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, s1, s2]; ring
  · subst e1 e2; funext i
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

theorem hypersimplex_mixture : ∀ (k : ℕ) (ρ : Fin M → ℝ), nfrac ρ = k → (∀ i, 0 ≤ ρ i ∧ ρ i ≤ 1) →
    ∑ i, ρ i = N → ∃ μ : Conf M N → ℝ, IsMixture ρ μ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ρ hk hbox hsum
  by_cases hfr : ∃ i, 0 < ρ i ∧ ρ i < 1
  · obtain ⟨i, hi⟩ := hfr
    -- a second fractional site exists (the sum is an integer)
    obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ 0 < ρ j ∧ ρ j < 1 := by
      by_contra hno
      push Not at hno
      have hint : ∀ l, l ≠ i → ρ l = 0 ∨ ρ l = 1 := by
        intro l hl
        rcases (hbox l).1.lt_or_eq with h | h
        · right; by_contra h1; exact absurd (hno l hl h) (not_le.mpr (lt_of_le_of_ne (hbox l).2 h1))
        · left; exact h.symm
      set T := (Finset.univ.erase i).filter fun l => ρ l = 1
      have hs : ∑ l, ρ l = ρ i + T.card := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        congr 1
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro l hl
        rcases hint l (Finset.mem_erase.mp hl).1 with h | h <;> simp [h]
      rw [hsum] at hs
      have : ρ i = (N : ℝ) - T.card := by linarith
      have hz : ((N : ℤ) - T.card : ℤ) = 0 ∨ ((N : ℤ) - T.card : ℤ) ≥ 1 ∨
          ((N : ℤ) - T.card : ℤ) ≤ -1 := by
        omega
      rcases hz with h | h | h
      · have : ρ i = 0 := by rw [this]; exact_mod_cast
          (by exact_mod_cast h : ((N : ℤ) - T.card : ℝ) = 0)
        linarith [hi.1]
      · have : (1 : ℝ) ≤ ρ i := by rw [this]; exact_mod_cast h
        linarith [hi.2]
      · have : ρ i ≤ -1 := by rw [this]; exact_mod_cast h
        linarith [hi.1]
    set e : Fin M → ℝ := fun l => (if l = i then 1 else 0) - (if l = j then 1 else 0)
    set a := min (1 - ρ i) (ρ j)
    set b := min (ρ i) (1 - ρ j)
    have ha : 0 < a := lt_min (by linarith [hi.2]) hj.1
    have hb : 0 < b := lt_min hi.1 (by linarith [hj.2])
    set ρp : Fin M → ℝ := fun l => ρ l + a * e l
    set ρm : Fin M → ℝ := fun l => ρ l - b * e l
    have hepos : ∀ l, l ≠ i → l ≠ j → e l = 0 := fun l h1 h2 => by simp [e, h1, h2]
    have hei : e i = 1 := by simp [e, hji.symm]
    have hej : e j = -1 := by simp [e, hji]
    have hsume : ∑ l, e l = 0 := by simp [e, Finset.sum_sub_distrib]
    -- the two endpoints are in the box, have the right sum and fewer fractional sites
    have hboxp : ∀ l, 0 ≤ ρp l ∧ ρp l ≤ 1 := by
      intro l
      by_cases hli : l = i
      · subst hli; simp only [ρp, hei, mul_one]
        exact ⟨by linarith [(hbox l).1], by linarith [min_le_left (1 - ρ l) (ρ j)]⟩
      · by_cases hlj : l = j
        · subst hlj; simp only [ρp, hej]
          exact ⟨by linarith [min_le_right (1 - ρ i) (ρ l)], by linarith [(hbox l).2]⟩
        · simp only [ρp, hepos l hli hlj, mul_zero, add_zero]; exact hbox l
    have hboxm : ∀ l, 0 ≤ ρm l ∧ ρm l ≤ 1 := by
      intro l
      by_cases hli : l = i
      · subst hli; simp only [ρm, hei, mul_one]
        exact ⟨by linarith [min_le_left (ρ l) (1 - ρ j)], by linarith [(hbox l).2]⟩
      · by_cases hlj : l = j
        · subst hlj; simp only [ρm, hej]
          exact ⟨by linarith [(hbox l).1], by linarith [min_le_right (ρ i) (1 - ρ l)]⟩
        · simp only [ρm, hepos l hli hlj, mul_zero, sub_zero]; exact hbox l
    have hsump : ∑ l, ρp l = N := by
      simp only [ρp, Finset.sum_add_distrib, ← Finset.mul_sum, hsume, mul_zero, add_zero, hsum]
    have hsumm : ∑ l, ρm l = N := by
      simp only [ρm, Finset.sum_sub_distrib, ← Finset.mul_sum, hsume, mul_zero, sub_zero, hsum]
    have hfewer : ∀ σ : Fin M → ℝ, (∀ l, l ≠ i → l ≠ j → σ l = ρ l) →
        (¬ (0 < σ i ∧ σ i < 1) ∨ ¬ (0 < σ j ∧ σ j < 1)) → nfrac σ < k := by
      intro σ hsame hone
      rw [← hk]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · rcases hone with h | h
        · exact ⟨i, by simp [hi], by simp [h]⟩
        · exact ⟨j, by simp [hj], by simp [h]⟩
      · intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
        by_cases hli : l = i
        · subst hli; exact hi
        · by_cases hlj : l = j
          · subst hlj; exact hj
          · rw [← hsame l hli hlj]; exact hl
    have hkp : nfrac ρp < k := by
      apply hfewer ρp (fun l h1 h2 => by simp [ρp, hepos l h1 h2])
      rcases min_choice (1 - ρ i) (ρ j) with h | h
      · left; simp only [ρp, hei, mul_one]; rw [show a = 1 - ρ i from h]; intro hc; linarith [hc.2]
      · right; simp only [ρp, hej]; rw [show a = ρ j from h]; intro hc; linarith [hc.1]
    have hkm : nfrac ρm < k := by
      apply hfewer ρm (fun l h1 h2 => by simp [ρm, hepos l h1 h2])
      rcases min_choice (ρ i) (1 - ρ j) with h | h
      · left; simp only [ρm, hei, mul_one]; rw [show b = ρ i from h]; intro hc; linarith [hc.1]
      · right; simp only [ρm, hej]; rw [show b = 1 - ρ j from h]; intro hc; linarith [hc.2]
    obtain ⟨μp, hμp⟩ := ih _ hkp ρp rfl hboxp hsump
    obtain ⟨μm, hμm⟩ := ih _ hkm ρm rfl hboxm hsumm
    set θ := b / (a + b)
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hcomb := mixture_combo hμp hμm hθ0 hθ1
    refine ⟨fun s => θ * μp s + (1 - θ) * μm s, ?_⟩
    have hρ : ρ = fun l => θ * ρp l + (1 - θ) * ρm l := by
      funext l
      simp only [ρp, ρm, θ]
      field_simp
      ring
    rw [hρ]; exact hcomb
  · -- no fractional site: ρ is a configuration
    push Not at hfr
    have h01 : ∀ l, ρ l = 0 ∨ ρ l = 1 := by
      intro l
      rcases (hbox l).1.lt_or_eq with h | h
      · right; by_contra h1; exact absurd (hfr l h) (not_le.mpr (lt_of_le_of_ne (hbox l).2 h1))
      · left; exact h.symm
    set S := Finset.univ.filter fun l => ρ l = 1
    have hcard : S.card = N := by
      have : (S.card : ℝ) = ∑ l, ρ l := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro l _
        rcases h01 l with h | h <;> simp [h]
      rw [hsum] at this; exact_mod_cast this
    set s0 : Conf M N := ⟨S, hcard⟩
    refine ⟨fun s => if s = s0 then
        1 else 0, fun s => by dsimp only; split_ifs <;> norm_num, by simp, ?_⟩
    funext l
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, occF, s0,
        S,
      Finset.mem_filter, true_and]
    rcases h01 l with h | h <;> simp [h]

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
    obtain ⟨μ, hμ0, hμ1, hμρ⟩ := hypersimplex_mixture _ ρ' rfl hbox' hsum'
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
