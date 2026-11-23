/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.PathSum.Resonance
public import LeanPool.DFT.Lattice.Generic.RationalFunctions

/-!
# Construction of the resonant point

Route sums are rational on generic points (`ratOn_DExp`, …); partner route sums are nonzero where
the target is the highest site (`Lval_ne_zero`); `exists_DExp_ne`: for every pair `c, y` some
injective potential has `DExp ≠ 0`.
-/

@[expose] public section

namespace DFT

section

open Matrix Filter Topology MvPolynomial

variable {M N : ℕ}

section
variable (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ)
    (rep : Fin M → Fin M)

lemma ratOn_Gr (b a : Fin M) : ∀ n p, RatOn
    (fun θ : Fin M → ℝ => Gr G t (fun i => θ (rep i)) b a n p) := by
  intro n
  induction n with
  | zero =>
    intro p
    simp only [Gr]
    exact RatOn.ite _ ((RatOn.const 1).div_sub _ _) (RatOn.const 0)
  | succ n ih =>
    intro p
    simp only [Gr]
    refine RatOn.ite _ (RatOn.div_sub (RatOn.sum _ fun r _ => ?_) _ _) (RatOn.const 0)
    exact RatOn.ite _ ((RatOn.const _).mul (ih r)) (RatOn.const 0)

lemma ratOn_Λ (b a π : Fin M) : ∀ n q, RatOn
    (fun θ : Fin M → ℝ => Λ G t (fun i => θ (rep i)) b a π n q) := by
  intro n
  induction n with
  | zero => intro q; simp only [Λ]; exact RatOn.const _
  | succ n ih =>
    intro q
    simp only [Λ]
    refine RatOn.ite _
        (RatOn.ite _ (RatOn.sum _ fun r _ => ?_) (RatOn.div_sub (RatOn.sum _ fun r _ => ?_) _ _))
      (RatOn.const 0)
    · exact RatOn.ite _ ((RatOn.const _).mul (ratOn_Gr G t rep b a n r)) (RatOn.const 0)
    · exact RatOn.ite _ ((RatOn.const _).mul (ih r)) (RatOn.const 0)

lemma ratOn_Lval (b a π : Fin M) : RatOn
    (fun θ : Fin M → ℝ => Lval G t (fun i => θ (rep i)) b a π) := by
  unfold Lval
  exact RatOn.sum _ fun p _ => RatOn.ite _ ((RatOn.const _).mul (ratOn_Λ G t rep b a π _ p))
      (RatOn.const 0)

lemma ratOn_alphaExp (b a : Fin M) : RatOn (fun u : Fin M → ℝ => alphaExp G t u b a) := by
  unfold alphaExp
  refine (RatOn.const _).add
      (RatOn.sum _ fun p _ => RatOn.ite _ ((RatOn.const _).mul ?_) (RatOn.const 0))
  simpa using ratOn_Gr G t id b a (G.dist b p) p

lemma ratOn_DExp (c y : Conf M N) : RatOn (fun u : Fin M → ℝ => DExp G t u c y) := by
  unfold DExp
  exact RatOn.sum _ fun σ _ => (RatOn.const _).mul (RatOn.prod _ fun l _ => ratOn_alphaExp G t _ _)

end

lemma exists_pred {G : SimpleGraph (Fin M)} (hG : G.Connected) {b q : Fin M} {n : ℕ}
    (h : G.dist b q = n + 1) : ∃ r, G.Adj q r ∧ G.dist b r = n := by
  obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist q b
  rw [SimpleGraph.dist_comm, h] at hw
  cases w with
  | nil => simp at hw
  | @cons _ r _ hadj w' =>
    refine ⟨r, hadj, ?_⟩
    have h1 : G.dist r b ≤ n := by
      have := SimpleGraph.dist_le w'; simp at hw; omega
    have h2 := hG.dist_triangle (u := b) (v := r) (w := q)
    rw [SimpleGraph.dist_comm (u := r) (v := q), SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at h2
    rw [SimpleGraph.dist_comm] at h1
    omega

/-- Positivity of the partner route sums when the target is the highest site. The hopping is assumed
unfrustrated in the simplest sense: all amplitudes on edges have the sign of a fixed `s`. -/
theorem Lval_ne_zero {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ}
    {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b)
    (us : Fin M → ℝ) (π a : Fin M) (hπa : π ≠ a) (hhigh : ∀ q, q ≠ a → q ≠ π → us q < us a) :
    Lval G t us π a π ≠ 0 := by
  have hpos : ∀ n q, G.dist π q = n → n < G.dist π a → 0 < Λ G t us π a π n q * (-s) ^ n := by
    intro n
    induction n with
    | zero =>
      intro q hq _
      have : q = π := (dist_eq_zero_iff hG).mp hq
      subst this; simp [Λ]
    | succ n ih =>
      intro q hq hlt
      have hqπ : q ≠ π := by intro h; subst h; simp at hq
      have hqa : q ≠ a := by intro h; subst h; omega
      have hden : 0 < us a - us q := sub_pos.mpr (hhigh q hqa hqπ)
      have hrw : Λ G t us π a π (n + 1) q * (-s) ^ (n + 1) =
          (∑ r, (if G.Adj q r ∧ G.dist π r = n then
              (s * t q r) * (Λ G t us π a π n r * (-s) ^ n) else 0)) /
            (us a - us q) := by
        simp only [Λ, ite_eq_left hq, ite_eq_right hqπ]
        rw [div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl; intro r _
        split_ifs
        · rw [pow_succ]; ring
        · simp
      rw [hrw]
      apply div_pos _ hden
      obtain ⟨r0, hr0, hdr0⟩ := exists_pred hG hq
      apply Finset.sum_pos' (fun r _ => by
        split_ifs with hr
        · exact (mul_pos (hts q r hr.1) (ih r hr.2 (by omega))).le
        · exact le_refl 0)
      exact ⟨r0, Finset.mem_univ _, by
        rw [ite_eq_left ⟨hr0, hdr0⟩]; exact mul_pos (hts q r0 hr0) (ih r0 hdr0 (by omega))⟩
  have hda : 0 < G.dist π a := by
    by_contra h0; push Not at h0
    exact hπa ((dist_eq_zero_iff hG).mp (by omega)).symm
  obtain ⟨p0, hp0, hdp0⟩ :=
      exists_pred hG (n := G.dist π a - 1) (by omega : G.dist π a = G.dist π a - 1 + 1)
  intro h0
  have hsum : 0 < ∑ p, (if G.Adj a p ∧ G.dist π p + 1 = G.dist π a then
      (s * t a p) * (Λ G t us π a π (G.dist π p) p * (-s) ^ (G.dist π p)) else 0) := by
    apply Finset.sum_pos' (fun p _ => by
      split_ifs with hp
      · exact (mul_pos (hts a p hp.1) (hpos _ p rfl (by omega))).le
      · exact le_refl 0)
    exact ⟨p0, Finset.mem_univ _, by
      rw [ite_eq_left ⟨hp0, by omega⟩]; exact mul_pos (hts a p0 hp0) (hpos _ p0 rfl (by omega))⟩
  have : Lval G t us π a π * (-s) ^ (G.dist π a) =
      ∑ p, (if G.Adj a p ∧ G.dist π p + 1 = G.dist π a then
      (s * t a p) * (Λ G t us π a π (G.dist π p) p * (-s) ^ (G.dist π p)) else 0) := by
    unfold Lval
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    split_ifs with hp
    · rw [← hp.2, pow_succ]; ring
    · simp
  rw [h0, zero_mul] at this
  exact hsum.ne' this.symm

end

section

open Matrix Filter Topology MvPolynomial

variable {M N : ℕ}

section
variable (c y : Conf M N) (σ0 : Equiv.Perm (Fin N))

/-- Partner (σ₀-start) of target slot `l`. -/
def partner (l : Fin N) : Fin M := τs c (σ0.symm l)

/-- Identify each moved partner with its target. -/
noncomputable def rep (z : Fin M) : Fin M :=
  if h : ∃ l, τs y l ∉ c.1 ∧ partner c σ0 l = z then τs y (Classical.choose h) else z

lemma partner_inj {l l' : Fin N} (h : partner c σ0 l = partner c σ0 l') : l = l' := by
  have := τs_injective c h; simpa using this

lemma rep_partner {l : Fin N} (hl : τs y l ∉ c.1) : rep c y σ0 (partner c σ0 l) = τs y l := by
  have hex : ∃ l', τs y l' ∉ c.1 ∧ partner c σ0 l' = partner c σ0 l := ⟨l, hl, rfl⟩
  simp only [rep, dite_eq_left hex]
  rw [partner_inj c σ0 (Classical.choose_spec hex).2]

lemma rep_target (hfix : ∀ l, τs y l ∈ c.1 → τs c (σ0.symm l) = τs y l) (l : Fin N) :
    rep c y σ0 (τs y l) = τs y l := by
  unfold rep
  rw [dite_eq_right]
  rintro ⟨l', hl', hp⟩
  have hc : τs y l ∈ c.1 := hp ▸ τs_mem c _
  have := partner_inj c σ0 (hp.trans (hfix l hc).symm)
  subst this; exact hl' hc

lemma rep_eq_target {l : Fin N} {z : Fin M} (h : rep c y σ0 z = τs y l) :
    z = τs y l ∨ (τs y l ∉ c.1 ∧ z = partner c σ0 l) := by
  unfold rep at h
  split_ifs at h with hex
  · have hspec := Classical.choose_spec hex
    have := τs_injective y h
    rw [this] at hspec
    exact Or.inr ⟨hspec.1, hspec.2.symm⟩
  · exact Or.inl h

end

theorem exists_DExp_ne {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ}
    {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (c y : Conf M N) :
    ∃ u : Fin M → ℝ, Function.Injective u ∧ DExp G t u c y ≠ 0 := by
  classical
  obtain ⟨σ0, h0, hfix⟩ := exists_opt_fixing hG c y
  set R := rep c y σ0
  set ι := {l : Fin N // τs y l ∉ c.1}
  -- 1. a common point θ where all partner route sums are nonzero
  have hpt : ∀ l : ι, ∃ θ : Fin M → ℝ, Function.Injective θ ∧
      Lval G t (fun i => θ (R i)) (partner c σ0 l.1) (τs y l.1) (partner c σ0 l.1) ≠ 0 := by
    intro l
    set a := τs y l.1
    refine ⟨fun i => if i = a then (M : ℝ) else (i : ℝ), ?_, ?_⟩
    · intro i j hij
      simp only at hij
      split_ifs at hij with hi hj hj
      · rw [hi, hj]
      · exfalso; have := j.isLt; have : (M : ℝ) = (j : ℕ) := hij; norm_cast at this; omega
      · exfalso; have := i.isLt; have : ((i : ℕ) : ℝ) = M := hij; norm_cast at this; omega
      · exact Fin.ext (by exact_mod_cast hij)
    · have hπa : partner c σ0 l.1 ≠ a := fun h => l.2 (by
        have hm : partner c σ0 l.1 ∈ c.1 := τs_mem c _
        rw [h] at hm; exact hm)
      apply Lval_ne_zero hG hts _ _ _ hπa
      intro q hqa hqπ
      have hRa : R a = a := rep_target c y σ0 hfix l.1
      have hRq : R q ≠ a := by
        intro h
        rcases rep_eq_target c y σ0 h with h1 | ⟨-, h1⟩
        · exact hqa h1
        · exact hqπ h1
      simp only [hRa, ite_eq_right hRq]
      exact_mod_cast (R q).isLt
  obtain ⟨θ, hθ, hθS, -⟩ := exists_common_ne (κ := Fin 0)
    (fun l : ι => fun θ => Lval G t (fun i => θ (R i)) (partner c σ0 l.1) (τs y l.1)
        (partner c σ0 l.1))
    (fun l => ratOn_Lval G t R _ _ _) hpt (fun k => k.elim0) (fun k => k.elim0)
  -- 2. the resonant point and the line
  set us : Fin M → ℝ := fun i => θ (R i)
  set δ : Fin M → ℝ := fun i => (i : ℝ)
  have hδinj : Function.Injective δ := fun i j h => by
    have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
    exact Fin.ext (by exact_mod_cast h')
  have hRtarget : ∀ l, R (τs y l) = τs y l := rep_target c y σ0 hfix
  have hRp : ∀ l, τs y l ∉ c.1 → R (partner c σ0 l) = τs y l := fun l hl => rep_partner c y σ0 hl
  have hReq : ∀ {l : Fin N} {z : Fin M}, R z = τs y l →
      z = τs y l ∨ (τs y l ∉ c.1 ∧ z = partner c σ0 l) := fun h => rep_eq_target c y σ0 h
  have hev := DExp_eventually_ne hG t c y σ0 h0 hfix us δ
    (fun l hl => by
      change θ (R (τs y l)) = θ (R (partner c σ0 l))
      rw [hRtarget, hRp l hl])
    (fun l hl z hz => by
      simp only [us, hRtarget] at hz
      rcases hReq (hθ hz) with h1 | ⟨-, h1⟩
      · exact Or.inl h1
      · exact Or.inr h1)
    (fun l hl z hz => by
      simp only [us, hRtarget] at hz
      rcases hReq (hθ hz) with h1 | ⟨h2, -⟩
      · exact h1
      · exact absurd hl h2)
    (fun l hl h => by
      have := hδinj h
      exact hl (this ▸ τs_mem c _))
    (fun l hl => hθS ⟨l, hl⟩)
  -- 3. the line is eventually injective
  have hinj : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), Function.Injective (uline us δ ε) := by
    have hpair : ∀ p : Fin M × Fin M, ∀ᶠ ε in 𝓝[≠] (0 : ℝ), p.1 ≠ p.2 →
        uline us δ ε p.1 ≠ uline us δ ε p.2 := by
      intro p
      by_cases hR : R p.1 = R p.2
      · filter_upwards [self_mem_nhdsWithin] with ε hε hne
        simp only [uline, us, hR]
        intro h
        have : ε * (δ p.1 - δ p.2) = 0 := by linarith
        rcases mul_eq_zero.mp this with h1 | h1
        · exact hε h1
        · exact hne (hδinj (sub_eq_zero.mp h1))
      · have hlim := (uline_tendsto us δ p.1).sub (uline_tendsto us δ p.2)
        have hne : us p.1 - us p.2 ≠ 0 := sub_ne_zero.mpr (fun h => hR (hθ h))
        filter_upwards [hlim.eventually_ne hne] with ε hε _
        exact fun h => hε (by rw [h, sub_self])
    filter_upwards [eventually_all.mpr hpair] with ε hε
    intro i j hij
    by_contra hne
    exact hε (i, j) hne hij
  obtain ⟨ε, hε1, hε2⟩ := (hev.and hinj).exists
  exact ⟨uline us δ ε, hε2, hε1⟩

end

end DFT
