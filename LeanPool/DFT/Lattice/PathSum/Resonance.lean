/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.PathSum.RouteSums
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.FunProp
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Ring

/-!
# The resonance argument

Along `u* + ε δ`, near a potential where each moving particle's target is degenerate with its
partner: plain and resonant limits of the route sums (`gr_tendsto_plain`, `gr_tendsto_hat`,
`Λ_supp`) and `DExp_eventually_ne`: the Slater-type sum is nonzero for all small `ε ≠ 0`.
-/

@[expose] public section

namespace DFT

section

open Matrix Filter Topology

variable {M : ℕ}

/-- The line of potentials. -/
def uline (us δ : Fin M → ℝ) (ε : ℝ) : Fin M → ℝ := fun i => us i + ε * δ i

lemma uline_tendsto (us δ : Fin M → ℝ) (i : Fin M) :
    Tendsto (fun ε => uline us δ ε i) (𝓝[≠] (0 : ℝ)) (𝓝 (us i)) := by
  have : Continuous fun ε : ℝ => us i + ε * δ i := by fun_prop
  have h := this.tendsto 0
  simp only [zero_mul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

section
variable (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ)

theorem gr_tendsto_plain (us δ : Fin M → ℝ) (b a : Fin M) (n0 : ℕ)
    (hA : ∀ r, G.dist b r ≤ n0 → us r ≠ us a) :
    ∀ n ≤ n0, ∀ q, Tendsto (fun ε => Gr G t (uline us δ ε) b a n q) (𝓝[≠] 0)
      (𝓝 (Gr G t us b a n q)) := by
  intro n
  induction n with
  | zero =>
    intro _ q
    by_cases hq : q = b
    · subst hq
      simp only [Gr]
      have hne : us a - us q ≠ 0 := sub_ne_zero.mpr (fun h => hA q (by simp) h.symm)
      exact tendsto_const_nhds.div ((uline_tendsto us δ a).sub (uline_tendsto us δ q)) hne
    · simp only [Gr, ite_eq_right hq]; exact tendsto_const_nhds
  | succ n ih =>
    intro hn q
    simp only [Gr]
    split_ifs with hq
    · have hne : us a - us q ≠ 0 := sub_ne_zero.mpr (fun h => hA q (by omega) h.symm)
      refine Tendsto.div (tendsto_finsetSum (f := fun r ε => if G.Adj q r ∧ G.dist b r = n then
          -t q r * Gr G t (uline us δ ε) b a n r else 0) _ fun r _ => ?_)
        ((uline_tendsto us δ a).sub (uline_tendsto us δ q)) hne
      by_cases h : G.Adj q r ∧ G.dist b r = n
      · simp only [ite_eq_left h]; exact tendsto_const_nhds.mul (ih (by omega) r)
      · simp only [ite_eq_right h]; exact tendsto_const_nhds
    · exact tendsto_const_nhds

/-- Limits of the hatted route sums. -/
noncomputable def Λ (us : Fin M → ℝ) (b a π : Fin M) : ℕ → Fin M → ℝ
  | 0, q => if q = b ∧ q = π then 1 else 0
  | n + 1, q => if G.dist b q = n + 1 then
      (if q = π then ∑ r, (if G.Adj q r ∧ G.dist b r = n then -t q r * Gr G t us b a n r else 0)
       else (∑ r, (if G.Adj q r ∧ G.dist b r = n then -t q r * Λ us b a π n r else 0)) /
           (us a - us q))
      else 0

theorem gr_tendsto_hat (us δ : Fin M → ℝ) (b a π : Fin M) (hπ : us a = us π)
    (hgen : ∀ z, us z = us a → z = a ∨ z = π) (hδ : δ a ≠ δ π) :
    ∀ n, n < G.dist b a → ∀ q, Tendsto
      (fun ε => (uline us δ ε a - uline us δ ε π) * Gr G t (uline us δ ε) b a n q) (𝓝[≠] 0)
      (𝓝 (Λ G t us b a π n q)) := by
  have hdiff : ∀ ε, uline us δ ε a - uline us δ ε π = ε * (δ a - δ π) := by
    intro ε; simp only [uline]; rw [hπ]; ring
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), uline us δ ε a - uline us δ ε π ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hdiff]; exact mul_ne_zero hε (sub_ne_zero.mpr hδ)
  have hzero : Tendsto (fun ε => uline us δ ε a - uline us δ ε π) (𝓝[≠] 0) (𝓝 0) := by
    have := (uline_tendsto us δ a).sub (uline_tendsto us δ π)
    rwa [hπ, sub_self] at this
  intro n
  induction n with
  | zero =>
    intro hn0 q
    by_cases hq : q = b
    · subst hq
      by_cases hqπ : q = π
      · subst hqπ
        have hL : Λ G t us q a q 0 q = 1 := by simp [Λ]
        rw [hL]
        apply tendsto_const_nhds.congr'
        filter_upwards [hev] with ε hε
        simp [Gr]; field_simp
      · have hL : Λ G t us q a π 0 q = 0 := by simp [Λ, hqπ]
        rw [hL]
        have hne : us a - us q ≠ 0 := by
          intro h; rcases hgen q (by linarith) with h1 | h1
          · subst h1; simp at hn0
          · exact hqπ h1
        have h2 := hzero.mul ((tendsto_const_nhds (x := (1 : ℝ))).div
          ((uline_tendsto us δ a).sub (uline_tendsto us δ q)) hne)
        rw [zero_mul] at h2
        refine h2.congr' (Eventually.of_forall fun ε => ?_)
        simp [Gr, Pi.div_apply]
    · have hL : Λ G t us b a π 0 q = 0 := by simp [Λ, hq]
      rw [hL]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun ε => ?_)
      simp [Gr, hq]
  | succ n ih =>
    intro hn q
    by_cases hq : G.dist b q = n + 1
    · by_cases hqπ : q = π
      · subst hqπ
        have hplain := gr_tendsto_plain G t us δ b a n (fun r hr h => by
          rcases hgen r h with h1 | h1
          · subst h1; omega
          · subst h1; omega)
        have hL : Λ G t us b a q (n + 1) q = ∑ r, (if G.Adj q r ∧ G.dist b r = n then
            -t q r * Gr G t us b a n r else 0) := by simp [Λ, hq]
        rw [hL]
        refine Tendsto.congr' ?_
            (tendsto_finsetSum (f := fun r ε => if G.Adj q r ∧ G.dist b r = n then
          -t q r * Gr G t (uline us δ ε) b a n r else 0) _ fun r _ => ?_)
        · filter_upwards [hev] with ε hε
          simp only [Gr, ite_eq_left hq]
          field_simp
        · by_cases h : G.Adj q r ∧ G.dist b r = n
          · simp only [ite_eq_left h]; exact tendsto_const_nhds.mul (hplain n le_rfl r)
          · simp only [ite_eq_right h]; exact tendsto_const_nhds
      · have hne : us a - us q ≠ 0 := by
          intro h; rcases hgen q (by linarith) with h1 | h1
          · subst h1; omega
          · exact hqπ h1
        have hL : Λ G t us b a π (n + 1) q = (∑ r, (if G.Adj q r ∧ G.dist b r = n then
            -t q r * Λ G t us b a π n r else 0)) / (us a - us q) := by simp [Λ, hq, hqπ]
        rw [hL]
        refine Tendsto.congr' ?_ (Tendsto.div (tendsto_finsetSum (f := fun r ε => if G.Adj q r ∧
          G.dist b r = n then
              -t q r * ((uline us δ ε a - uline us δ ε π) * Gr G t (uline us δ ε) b a n r)
          else 0) _ fun r _ => ?_)
          ((uline_tendsto us δ a).sub (uline_tendsto us δ q)) hne)
        · refine Eventually.of_forall fun ε => ?_
          simp only [Gr, ite_eq_left hq, Pi.div_apply]
          rw [mul_div_assoc', Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl; intro r _
          split_ifs <;> ring
        · by_cases h : G.Adj q r ∧ G.dist b r = n
          · simp only [ite_eq_left h]; exact tendsto_const_nhds.mul (ih (by omega) r)
          · simp only [ite_eq_right h]; exact tendsto_const_nhds
    · have hL : Λ G t us b a π (n + 1) q = 0 := by simp [Λ, hq]
      rw [hL]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun ε => ?_)
      simp [Gr, hq]

/-- `Λ n q ≠ 0` only if the partner lies on a shortest route from `b` to `q`. -/
theorem Λ_supp (hG : G.Connected) (us : Fin M → ℝ) (b a π : Fin M) :
    ∀ n q, Λ G t us b a π n q ≠ 0 → G.dist b π + G.dist π q = n ∧ G.dist b q = n := by
  intro n
  induction n with
  | zero =>
    intro q hq
    simp only [Λ] at hq
    split_ifs at hq with h
    · obtain ⟨rfl, rfl⟩ := h; simp
    · exact absurd rfl hq
  | succ n ih =>
    intro q hq
    simp only [Λ] at hq
    split_ifs at hq with hd hqπ
    · subst hqπ; simp [hd]
    · have hnum : ∑ r, (if G.Adj q r ∧ G.dist b r = n then -t q r * Λ G t us b a π n r else 0) ≠
        0 := by
        intro h0; apply hq; rw [h0, zero_div]
      obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnum
      split_ifs at hr with hrq
      · have hΛ : Λ G t us b a π n r ≠ 0 := by intro h0; apply hr; rw [h0, mul_zero]
        obtain ⟨h1, -⟩ := ih r hΛ
        have h2 : G.dist π q ≤ G.dist π r + 1 := by
          have := hG.dist_triangle (u := π) (v := r) (w := q)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hrq.1.symm] at this; exact this
        have h3 := hG.dist_triangle (u := b) (v := π) (w := q)
        exact ⟨by omega, hd⟩
      · exact absurd rfl hr
    · exact absurd rfl hq

end

end

section

open Matrix Filter Topology

variable {M N : ℕ}

section
variable (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ)

/-- Limit value of a resonant factor. -/
noncomputable def Lval (us : Fin M → ℝ) (b a π : Fin M) : ℝ :=
  ∑ p, (if G.Adj a p ∧ G.dist b p + 1 = G.dist b a then
      -t a p * Λ G t us b a π (G.dist b p) p else 0)

lemma alphaExp_self (u : Fin M → ℝ) (b : Fin M) : alphaExp G t u b b = 1 := by
  simp [alphaExp, SimpleGraph.dist_self]

lemma factor_moved_tendsto (us δ : Fin M → ℝ) (b a π : Fin M) (hab : a ≠ b) (hπ : us a = us π)
    (hgen : ∀ z, us z = us a → z = a ∨ z = π) (hδ : δ a ≠ δ π) :
    Tendsto (fun ε => (uline us δ ε a - uline us δ ε π) * alphaExp G t (uline us δ ε) b a) (𝓝[≠] 0)
      (𝓝 (Lval G t us b a π)) := by
  have hfun : (fun ε => (uline us δ ε a - uline us δ ε π) * alphaExp G t (uline us δ ε) b a) =
      fun ε => ∑ p, (if G.Adj a p ∧ G.dist b p + 1 = G.dist b a then
        -t a p * ((uline us δ ε a - uline us δ ε π) * Gr G t (uline us δ ε) b a (G.dist b p) p) else
            0) := by
    funext ε
    simp only [alphaExp, ite_eq_right hab, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    split_ifs <;> ring
  rw [hfun]
  apply tendsto_finsetSum; intro p _
  by_cases h : G.Adj a p ∧ G.dist b p + 1 = G.dist b a
  · simp only [ite_eq_left h]
    exact tendsto_const_nhds.mul (gr_tendsto_hat G t us δ b a π hπ hgen hδ _ (by omega) p)
  · simp only [ite_eq_right h]; exact tendsto_const_nhds

lemma Lval_through (hG : G.Connected) (us : Fin M → ℝ) (b a π : Fin M)
    (h : Lval G t us b a π ≠ 0) : G.dist b π + G.dist π a = G.dist b a := by
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hp with hc
  · have hΛ : Λ G t us b a π (G.dist b p) p ≠ 0 := by intro h0; apply hp; rw [h0, mul_zero]
    obtain ⟨h1, -⟩ := Λ_supp G t hG us b a π _ p hΛ
    have h2 : G.dist π a ≤ G.dist π p + 1 := by
      have := hG.dist_triangle (u := π) (v := p) (w := a)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hc.1.symm] at this; exact this
    have h3 := hG.dist_triangle (u := b) (v := π) (w := a)
    omega
  · exact absurd rfl hp

lemma factor_common_tendsto (hG : G.Connected) (us δ : Fin M → ℝ) (b a : Fin M)
    (hA : ∀ z, us z = us a → z = a) :
    Tendsto (fun ε => alphaExp G t (uline us δ ε) b a) (𝓝[≠] 0) (𝓝 (alphaExp G t us b a)) := by
  by_cases hab : a = b
  · subst hab; simp only [alphaExp_self]; exact tendsto_const_nhds
  · have hpos : 0 < G.dist b a := by
      by_contra h0; push Not at h0
      have : G.dist b a = 0 := by omega
      exact hab ((dist_eq_zero_iff hG).mp this)
    have hfun : (fun ε => alphaExp G t (uline us δ ε) b a) = fun ε => ∑ p,
        (if G.Adj a p ∧ G.dist b p + 1 = G.dist b a then
            -t a p * Gr G t (uline us δ ε) b a (G.dist b p) p
        else 0) := by
      funext ε; simp [alphaExp, hab]
    have hlim : alphaExp G t us b a = ∑ p,
        (if G.Adj a p ∧ G.dist b p + 1 = G.dist b a then
            -t a p * Gr G t us b a (G.dist b p) p else 0) := by
      simp [alphaExp, hab]
    rw [hfun, hlim]
    apply tendsto_finsetSum; intro p _
    by_cases h : G.Adj a p ∧ G.dist b p + 1 = G.dist b a
    · simp only [ite_eq_left h]
      refine tendsto_const_nhds.mul
          (gr_tendsto_plain G t us δ b a (G.dist b a - 1) ?_ _ (by omega) p)
      intro r hr hra
      have := hA r hra; subst this; omega
    · simp only [ite_eq_right h]; exact tendsto_const_nhds

end

/-- **Resonance argument.** Along `u* + ε δ`, `DExp ≠ 0` for all small `ε ≠ 0`. -/
theorem DExp_eventually_ne {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    (c y : Conf M N) (σ0 : Equiv.Perm (Fin N)) (h0 : isOpt G c y σ0)
    (hfix : ∀ l, τs y l ∈ c.1 → τs c (σ0.symm l) = τs y l) (us δ : Fin M → ℝ)
    (hV : ∀ l, τs y l ∉ c.1 → us (τs y l) = us (τs c (σ0.symm l)))
    (hgenM : ∀ l, τs y l ∉ c.1 → ∀ z, us z = us (τs y l) → z = τs y l ∨ z = τs c (σ0.symm l))
    (hgenC : ∀ l, τs y l ∈ c.1 → ∀ z, us z = us (τs y l) → z = τs y l)
    (hδ : ∀ l, τs y l ∉ c.1 → δ (τs y l) ≠ δ (τs c (σ0.symm l)))
    (hS : ∀ l, τs y l ∉ c.1 → Lval G t us (τs c (σ0.symm l)) (τs y l) (τs c (σ0.symm l)) ≠ 0) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), DExp G t (uline us δ ε) c y ≠ 0 := by
  classical
  set opt := Finset.univ.filter (isOpt G c y)
  set dfac : ℝ → Fin N → ℝ := fun ε l => if τs y l ∉ c.1 then
    uline us δ ε (τs y l) - uline us δ ε (τs c (σ0.symm l)) else 1
  set fac : Equiv.Perm (Fin N) → Fin N → ℝ → ℝ := fun σ l ε =>
    dfac ε l * alphaExp G t (uline us δ ε) (τs c (σ.symm l)) (τs y l)
  set lim : Equiv.Perm (Fin N) → Fin N → ℝ := fun σ l => if τs y l ∉ c.1 then
    Lval G t us (τs c (σ.symm l)) (τs y l) (τs c (σ0.symm l))
    else alphaExp G t us (τs c (σ.symm l)) (τs y l)
  set H : ℝ → ℝ := fun ε => ∑ σ ∈ opt, (Equiv.Perm.sign σ : ℝ) * ∏ l, fac σ l ε
  -- (1) limits of the factors
  have hfac : ∀ σ l, Tendsto (fac σ l) (𝓝[≠] 0) (𝓝 (lim σ l)) := by
    intro σ l
    by_cases hm : τs y l ∉ c.1
    · simp only [fac, dfac, lim, ite_eq_left hm]
      have hab : τs y l ≠ τs c (σ.symm l) := fun h => hm (h ▸ τs_mem c _)
      exact factor_moved_tendsto G t us δ _ _ _ hab (hV l hm) (hgenM l hm) (hδ l hm)
    · simp only [fac, dfac, lim, ite_eq_right hm, one_mul]
      push Not at hm
      exact factor_common_tendsto G t hG us δ _ _ (hgenC l hm)
  have hH : Tendsto H (𝓝[≠] 0) (𝓝 (∑ σ ∈ opt, (Equiv.Perm.sign σ : ℝ) * ∏ l, lim σ l)) := by
    apply tendsto_finsetSum; intro σ _
    exact tendsto_const_nhds.mul (tendsto_finsetProd _ (fun l _ => hfac σ l))
  -- (2) only σ0 survives in the limit
  have hσ0 : σ0 ∈ opt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
  have hlim0 : ∑ σ ∈ opt, (Equiv.Perm.sign σ : ℝ) * ∏ l, lim σ l =
      (Equiv.Perm.sign σ0 : ℝ) * ∏ l, lim σ0 l := by
    apply Finset.sum_eq_single σ0
    · intro σ hσ hne
      have hσo : isOpt G c y σ := (Finset.mem_filter.mp hσ).2
      have : ∏ l, lim σ l = 0 := by
        by_contra hprod
        apply hne
        apply opt_unique_of_through hG c y h0 hfix hσo
        intro l hm
        have hl : lim σ l ≠ 0 := fun h' => hprod (Finset.prod_eq_zero (Finset.mem_univ l) h')
        simp only [lim, ite_eq_left hm] at hl
        exact Lval_through G t hG us _ _ _ hl
      rw [this, mul_zero]
    · intro h; exact absurd hσ0 h
  -- (3) the σ0 limit is nonzero
  have hne0 : (Equiv.Perm.sign σ0 : ℝ) * ∏ l, lim σ0 l ≠ 0 := by
    refine mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign σ0) with h | h <;> simp [h])
      (Finset.prod_ne_zero_iff.mpr fun l _ => ?_)
    by_cases hm : τs y l ∉ c.1
    · simp only [lim, ite_eq_left hm]; exact hS l hm
    · simp only [lim, ite_eq_right hm]
      push Not at hm
      rw [hfix l hm, alphaExp_self]; exact one_ne_zero
  rw [hlim0] at hH
  -- (4) H is eventually nonzero, and H = (Π dfac) · DExp
  filter_upwards [hH.eventually_ne hne0] with ε hε
  intro hD
  apply hε
  have hfact : H ε = (∏ l, dfac ε l) * DExp G t (uline us δ ε) c y := by
    simp only [H, fac, DExp, Finset.prod_mul_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro σ _; ring
  rw [hfact, hD, mul_zero]

end

end DFT
