/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Cocycle

/-!
# The slow projection (`lem:topdecomp`, deterministic core)

`proof_met.tex` l.790--905 builds the projection `Π_ω` onto the slow space as the limit of
nonlinear approximants `Π^{(n)}_ω x = x - e_n`, `e_n ∈ E(ω)` chosen so that
`‖𝓛^{(n)}_ω(x - e_n)‖ ≤ e^ε ρ_{m₁+1}(𝓛^{(n)}_ω)‖x - e_n‖`, and then proves linearity of the limit
by estimating the defect `Π^{(n)}(b+tc) - Π^{(n)}b - tΠ^{(n)}c`.

This file isolates the part of that argument that involves no measure theory: a sequence of
operators `T_{n+1} = S_n ∘ T_n` with exponential rates, a subspace `E` grown at the fast rate,
and *any* choice of slow representatives `y_n x ∈ x + E`.

**Departure from the paper: linearity by uniqueness.** Instead of estimating the defect, the
limit `P x` is shown to be the *only* point of `x + E` growing at the slow rate θ
(`SlowRepHyp.exists_proj`, last clause): two such points differ by a vector of `E`, which grows
at the fast rate `α > θ`. `P(b + tc)` and `Pb + tPc` are both such points, so they agree. The
same uniqueness gives `P ∘ P = P` and `P|_E = 0` downstream, and makes the limit independent of
which representatives were chosen, which is what lets the measurable selection be made
separately for each fixed `x`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open Filter Topology MeasureTheory TopologicalSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A slow representative at one time is controlled by the offset it removes. -/
theorem norm_slowRep_le {T : X →L[ℝ] X} {E : Submodule ℝ X} {g ρ : ℝ}
    (hg : g ≤ growth T E) (hgpos : 0 < g) (h4 : 4 * ρ ≤ g) {x y : X} (hxy : x - y ∈ E)
    (hy : ‖T y‖ ≤ 2 * ρ * ‖y‖) :
    ‖y‖ ≤ 2 * (1 + ‖T‖ / g) * ‖x‖ := by
  have he : g * ‖x - y‖ ≤ ‖T x‖ + ‖T y‖ := by
    calc g * ‖x - y‖ ≤ growth T E * ‖x - y‖ := by gcongr
      _ ≤ ‖T (x - y)‖ := growth_mul_norm_le T hxy
      _ ≤ ‖T x‖ + ‖T y‖ := by rw [map_sub]; exact norm_sub_le _ _
  have hTx : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
  have hy' : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
  have hρ : 2 * ρ * ‖y‖ ≤ g / 2 * ‖y‖ := by
    gcongr; linarith
  have h1 : ‖x - y‖ ≤ ‖T‖ / g * ‖x‖ + ‖y‖ / 2 := by
    have hk : ‖x - y‖ * g ≤ (‖T‖ / g * ‖x‖ + ‖y‖ / 2) * g := by
      rw [add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self hgpos.ne',
        mul_one]
      nlinarith [norm_nonneg y]
    exact le_of_mul_le_mul_right hk hgpos
  linarith

/-- Two slow representatives of the same point at consecutive times differ by a vector of `E`,
which the later operator must grow. -/
theorem growth_mul_norm_sub_le {T S : X →L[ℝ] X} {E : Submodule ℝ X} {x y y' : X}
    (hy : x - y ∈ E) (hy' : x - y' ∈ E) :
    growth (S.comp T) E * ‖y' - y‖ ≤ ‖S.comp T y'‖ + ‖S‖ * ‖T y‖ := by
  have hmem : y' - y ∈ E := by
    have := E.sub_mem hy hy'
    rwa [sub_sub_sub_cancel_left] at this
  calc growth (S.comp T) E * ‖y' - y‖ ≤ ‖S.comp T (y' - y)‖ := growth_mul_norm_le _ hmem
    _ ≤ ‖S.comp T y'‖ + ‖S (T y)‖ := by
        rw [map_sub]; exact (norm_sub_le _ _).trans (by simp)
    _ ≤ ‖S.comp T y'‖ + ‖S‖ * ‖T y‖ := by gcongr; exact S.le_opNorm _

/-- **Existence of a slow representative at one time.** If `E` is `m`-dimensional and
`ρ_{m+1}(T) < c ≤ g_T(E)`, then every `x ∉ E` has a translate `x - e`, `e ∈ E`, with
`‖T(x-e)‖ < c‖x-e‖`: the `(m+1)`-dimensional space `E ⊕ ℝx` has growth `< c`, and a slow unit
vector in it cannot lie in `E`. -/
theorem exists_slow_translate {T : X →L[ℝ] X} {E : Submodule ℝ X} [FiniteDimensional ℝ E]
    {m : ℕ} (hm : Module.finrank ℝ E = m) {c : ℝ} (hρ : bernsteinNumber T (m + 1) < c)
    (hc : c ≤ growth T E) {x : X} (hx : x ∉ E) :
    ∃ e ∈ E, ‖T (x - e)‖ < c * ‖x - e‖ := by
  set W : Submodule ℝ X := E ⊔ Submodule.span ℝ {x} with hW
  have : FiniteDimensional ℝ W := Submodule.finiteDimensional_sup _ _
  have hWrank : Module.finrank ℝ W = m + 1 := by
    have hdisj : Disjoint E (Submodule.span ℝ {x}) := by
      rw [Submodule.disjoint_span_singleton' (by rintro rfl; exact hx E.zero_mem)]
      exact hx
    have := Submodule.finrank_sup_add_finrank_inf_eq E (Submodule.span ℝ {x})
    rw [hdisj.eq_bot, finrank_bot, add_zero, hm,
      finrank_span_singleton (by rintro rfl; exact hx E.zero_mem)] at this
    exact this
  let V : GrassmannianFin X (m + 1) := ⟨W, inferInstance, hWrank⟩
  have hgW : growth T W < c := by
    refine lt_of_le_of_lt ?_ hρ
    exact le_csSup (s := Set.range fun V : GrassmannianFin X (m + 1) => growth T V.1)
      ⟨‖T‖, by rintro _ ⟨U, rfl⟩; exact growth_le_opNorm T _⟩ ⟨V, rfl⟩
  have hne : (Metric.sphere (0 : X) 1 ∩ (W : Set X)).Nonempty := by
    refine ⟨‖x‖⁻¹ • x, ?_,
      W.smul_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))⟩
    have : x ≠ 0 := by rintro rfl; exact hx E.zero_mem
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 this)]
  obtain ⟨_, ⟨w, ⟨hw1, hwW⟩, rfl⟩, hwlt⟩ := exists_lt_of_csInf_lt (hne.image _) hgW
  obtain ⟨e', he', z, hz, rfl⟩ := Submodule.mem_sup.1 hwW
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hw1' : ‖e' + a • x‖ = 1 := mem_sphere_zero_iff_norm.1 hw1
  by_cases ha : a = 0
  · subst ha
    simp only [zero_smul, add_zero] at hw1' hwlt
    have := growth_mul_norm_le T he'
    rw [hw1', mul_one] at this
    linarith
  · refine ⟨-a⁻¹ • e', E.smul_mem _ he', ?_⟩
    have hxe : x - -a⁻¹ • e' = a⁻¹ • (e' + a • x) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul, neg_smul, sub_neg_eq_add, add_comm]
    rw [hxe, map_smul, norm_smul, norm_smul, hw1', mul_one, mul_comm c]
    exact mul_lt_mul_of_pos_left hwlt (norm_pos_iff.2 (inv_ne_zero ha))

section Sequence

variable {T S : ℕ → X →L[ℝ] X} {E : Submodule ℝ X} {ρ : ℕ → ℝ} {y : ℕ → X → X}
  {A α β s : ℝ} {N : ℕ}

/-- The standing hypotheses of the slow-projection construction, from time `N` on: rates `A`,
`α`, `β`, `s` for `‖T_n‖`, `g(T_n, E)`, the slow scale `ρ_n` and the one-step factor `‖S_n‖`, and
a slow representative `y_n x ∈ x + E` of every `x` at every time. -/
def SlowRepHyp (T S : ℕ → X →L[ℝ] X) (E : Submodule ℝ X) (ρ : ℕ → ℝ) (y : ℕ → X → X)
    (A α β s : ℝ) (N : ℕ) : Prop :=
  ∀ n ≥ N, ‖T n‖ ≤ Real.exp (n * A) ∧ Real.exp (n * α) ≤ growth (T n) E ∧
    ρ n ≤ Real.exp (n * β) ∧ ‖S n‖ ≤ Real.exp (n * s) ∧ 4 * ρ n ≤ growth (T n) E ∧
    ∀ x, x - y n x ∈ E ∧ ‖T n (y n x)‖ ≤ 2 * ρ n * ‖y n x‖

theorem SlowRepHyp.norm_le (h : SlowRepHyp T S E ρ y A α β s N) (hαA : α ≤ A) {n : ℕ}
    (hn : N ≤ n) (x : X) : ‖y n x‖ ≤ 4 * Real.exp (n * (A - α)) * ‖x‖ := by
  obtain ⟨hT, hg, -, -, h4, hy⟩ := h n hn
  have hgpos : 0 < growth (T n) E := lt_of_lt_of_le (Real.exp_pos _) hg
  refine (norm_slowRep_le le_rfl hgpos h4 (hy x).1 (hy x).2).trans ?_
  have hratio : ‖T n‖ / growth (T n) E ≤ Real.exp (n * (A - α)) := by
    rw [div_le_iff₀ hgpos, mul_sub, Real.exp_sub]
    calc ‖T n‖ ≤ Real.exp (n * A) := hT
      _ = Real.exp (n * A) / Real.exp (n * α) * Real.exp (n * α) := by
          rw [div_mul_cancel₀ _ (Real.exp_pos _).ne']
      _ ≤ Real.exp (n * A) / Real.exp (n * α) * growth (T n) E := by gcongr
  have hone : 1 ≤ Real.exp (n * (A - α)) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)

theorem SlowRepHyp.dist_succ_le (h : SlowRepHyp T S E ρ y A α β s N)
    (hTS : ∀ n, T (n + 1) = (S n).comp (T n)) (hs : 0 ≤ s) (hαA : α ≤ A) {n : ℕ}
    (hn : N ≤ n) (x : X) :
    dist (y n x) (y (n + 1) x) ≤
      8 * (Real.exp (β + A - 2 * α) + Real.exp (-α)) *
        Real.exp (β + A - 2 * α + s) ^ n * ‖x‖ := by
  obtain ⟨-, -, hρ, hS, -, hy⟩ := h n hn
  obtain ⟨-, hg1, hρ1, -, -, hy1⟩ := h (n + 1) (by omega)
  have hb := h.norm_le hαA hn x
  have hb1 := h.norm_le hαA (by omega : N ≤ n + 1) x
  have hd := growth_mul_norm_sub_le (T := T n) (S := S n) (hy x).1 (hy1 x).1
  rw [← hTS] at hd
  push_cast at hg1 hρ1 hb1
  have hx := norm_nonneg x
  -- `e^{(n+1)α} ‖d‖` against the two error terms
  have key : Real.exp ((n + 1) * α) * ‖y (n + 1) x - y n x‖ ≤
      8 * Real.exp ((n + 1) * (β + A - α)) * ‖x‖ + 8 * Real.exp (n * (s + β + A - α)) * ‖x‖ := by
    calc Real.exp ((n + 1) * α) * ‖y (n + 1) x - y n x‖
        ≤ growth (T (n + 1)) E * ‖y (n + 1) x - y n x‖ := by gcongr
      _ ≤ ‖T (n + 1) (y (n + 1) x)‖ + ‖S n‖ * ‖T n (y n x)‖ := hd
      _ ≤ 2 * Real.exp ((n + 1) * β) * (4 * Real.exp ((n + 1) * (A - α)) * ‖x‖) +
          Real.exp (n * s) * (2 * Real.exp (n * β) * (4 * Real.exp (n * (A - α)) * ‖x‖)) := by
        gcongr
        · exact (hy1 x).2.trans (by gcongr)
        · exact (hy x).2.trans (by gcongr)
      _ = 8 * Real.exp ((n + 1) * (β + A - α)) * ‖x‖ +
          8 * Real.exp (n * (s + β + A - α)) * ‖x‖ := by
        have e1 : Real.exp ((n + 1) * β) * Real.exp ((n + 1) * (A - α)) =
            Real.exp ((n + 1) * (β + A - α)) := by rw [← Real.exp_add]; congr 1; ring
        have e2 : Real.exp (n * s) * Real.exp (n * β) * Real.exp (n * (A - α)) =
            Real.exp (n * (s + β + A - α)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [← e1, ← e2]; ring
  rw [dist_comm, dist_eq_norm, ← Real.exp_nat_mul]
  have hpos : 0 < Real.exp ((n + 1) * α) := Real.exp_pos _
  refine le_of_mul_le_mul_left (key.trans ?_) hpos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have f1 : Real.exp ((n + 1) * (β + A - α)) ≤
      Real.exp ((n + 1) * α) * (Real.exp (β + A - 2 * α) * Real.exp (n * (β + A - 2 * α + s))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have f2 : Real.exp (n * (s + β + A - α)) =
      Real.exp ((n + 1) * α) * (Real.exp (-α) * Real.exp (n * (β + A - 2 * α + s))) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [f2]
  nlinarith [Real.exp_pos ((n + 1) * α), Real.exp_pos (-α), Real.exp_pos (β + A - 2 * α),
    Real.exp_pos (n * (β + A - 2 * α + s))]

/-- **The slow projection.** Under `SlowRepHyp`, with the contraction rate
`κ = β + A - 2α + s < 0` and the resulting slow rate `θ = A + κ` below the fast rate `α`, the slow
representatives converge, geometrically and uniformly on bounded sets, to a bounded linear map
`P` with `x - P x ∈ E`. `P x` is the *only* point of `x + E` growing at rate `θ`, which is what
makes `P` linear: no linearity is asked of the representatives themselves. -/
theorem SlowRepHyp.exists_proj [CompleteSpace X] (h : SlowRepHyp T S E ρ y A α β s N)
    (hTS : ∀ n, T (n + 1) = (S n).comp (T n)) (hs : 0 ≤ s) (hαA : α ≤ A)
    (hκ : β + A - 2 * α + s < 0) (hθ : A + (β + A - 2 * α + s) < α)
    (hE : IsClosed (E : Set X)) :
    ∃ P : X →L[ℝ] X, (∀ x, Tendsto (fun n => y n x) atTop (𝓝 (P x))) ∧
      (∀ x, x - P x ∈ E) ∧
      (∃ C, ∀ n ≥ N, ∀ x, ‖T n (P x)‖ ≤ C * Real.exp (n * (A + (β + A - 2 * α + s))) * ‖x‖) ∧
      (∀ x z, x - z ∈ E → (∃ D, ∀ᶠ n in atTop,
          ‖T n z‖ ≤ D * Real.exp (n * (A + (β + A - 2 * α + s)))) → z = P x) := by
  set κ := β + A - 2 * α + s with hκdef
  set θ := A + κ with hθdef
  set r := Real.exp κ with hrdef
  set K := 8 * (Real.exp (β + A - 2 * α) + Real.exp (-α)) with hKdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 hκ
  have hK0 : 0 ≤ K := by positivity
  have hstep : ∀ x, ∀ n ≥ N, dist (y n x) (y (n + 1) x) ≤ K * ‖x‖ * r ^ n := fun x n hn =>
    (h.dist_succ_le hTS hs hαA hn x).trans_eq (by ring)
  have hcauchy : ∀ x, CauchySeq fun n => y n x := fun x =>
    cauchySeq_of_eventually_dist_le_geom _ hr0 hr1 (eventually_atTop.2 ⟨N, hstep x⟩)
  choose Lf hLf using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  -- the tail bound, from time `N` on
  have htail : ∀ x, ∀ n ≥ N, ‖y n x - Lf x‖ ≤ K * ‖x‖ * r ^ n / (1 - r) := by
    intro x n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + N := ⟨n - N, by omega⟩
    have hshift : ∀ j : ℕ, dist (y (j + N) x) (y (j + 1 + N) x) ≤ K * ‖x‖ * r ^ N * r ^ j := by
      intro j
      rw [show j + 1 + N = j + N + 1 by omega]
      exact (hstep x (j + N) (by omega)).trans_eq (by rw [pow_add]; ring)
    have hlim : Tendsto (fun j : ℕ => y (j + N) x) atTop (𝓝 (Lf x)) :=
      (hLf x).comp (tendsto_add_atTop_nat N)
    rw [← dist_eq_norm]
    exact (dist_le_of_le_geometric_of_tendsto (r := r) (C := K * ‖x‖ * r ^ N)
      hr1 hshift hlim k).trans_eq
      (by rw [pow_add]; ring)
  have h1r : 0 < 1 - r := by linarith
  set C0 := K / (1 - r) + 8 with hC0
  have hslow : ∀ x, ∀ n ≥ N, ‖T n (Lf x)‖ ≤ C0 * Real.exp (n * θ) * ‖x‖ := by
    intro x n hn
    obtain ⟨hT, -, hρ, -, -, hy⟩ := h n hn
    have hb := h.norm_le hαA hn x
    have hx := norm_nonneg x
    have e1 : Real.exp (n * A) * r ^ n = Real.exp (n * θ) := by
      rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; rw [hθdef]; ring
    have e2 : Real.exp (n * β) * Real.exp (n * (A - α)) ≤ Real.exp (n * θ) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by rw [hθdef, hκdef]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    calc ‖T n (Lf x)‖ = ‖T n (Lf x - y n x) + T n (y n x)‖ := by rw [← map_add, sub_add_cancel]
      _ ≤ ‖T n‖ * ‖y n x - Lf x‖ + 2 * ρ n * ‖y n x‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ (hy x).2)
          rw [← norm_neg, ← map_neg, neg_sub]; exact (T n).le_opNorm _
      _ ≤ Real.exp (n * A) * (K * ‖x‖ * r ^ n / (1 - r)) +
          2 * Real.exp (n * β) * (4 * Real.exp (n * (A - α)) * ‖x‖) := by
          gcongr
          · exact htail x n hn
      _ = K / (1 - r) * (Real.exp (n * A) * r ^ n) * ‖x‖ +
          8 * (Real.exp (n * β) * Real.exp (n * (A - α))) * ‖x‖ := by ring
      _ ≤ K / (1 - r) * Real.exp (n * θ) * ‖x‖ + 8 * Real.exp (n * θ) * ‖x‖ := by
          rw [e1]; gcongr
      _ = C0 * Real.exp (n * θ) * ‖x‖ := by ring
  have hmem : ∀ x, x - Lf x ∈ E := fun x =>
    hE.mem_of_tendsto ((tendsto_const_nhds (x := x)).sub (hLf x))
      (eventually_atTop.2 ⟨N, fun n hn => (h n hn).2.2.2.2.2 x |>.1⟩)
  have hdecay : Tendsto (fun n : ℕ => Real.exp ((θ - α) * n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (by linarith)).2 tendsto_natCast_atTop_atTop)
  have huniq : ∀ x z, x - z ∈ E → (∃ D, ∀ᶠ n in atTop, ‖T n z‖ ≤ D * Real.exp (n * θ)) →
      z = Lf x := by
    rintro x z hz ⟨D, hD⟩
    have hu : z - Lf x ∈ E := by
      have := E.sub_mem (hmem x) hz
      rwa [sub_sub_sub_cancel_left] at this
    have hle : ∀ᶠ n : ℕ in atTop, ‖z - Lf x‖ ≤ (D + C0 * ‖x‖) * Real.exp ((θ - α) * n) := by
      filter_upwards [hD, eventually_ge_atTop N] with n hDn hn
      obtain ⟨-, hg, -, -, -, -⟩ := h n hn
      have hgrow := growth_mul_norm_le (T n) hu
      have hTu : ‖T n (z - Lf x)‖ ≤ (D + C0 * ‖x‖) * Real.exp (n * θ) := by
        rw [map_sub]
        refine (norm_sub_le _ _).trans ?_
        have := hslow x n hn
        linarith
      have hexp : Real.exp ((θ - α) * n) = Real.exp (n * θ) / Real.exp (n * α) := by
        rw [← Real.exp_sub]; congr 1; ring
      rw [hexp, mul_div_assoc', le_div_iff₀ (Real.exp_pos _), mul_comm]
      nlinarith [norm_nonneg (z - Lf x)]
    have h0 : ‖z - Lf x‖ ≤ 0 := by
      have := hdecay.const_mul (D + C0 * ‖x‖)
      rw [mul_zero] at this
      exact ge_of_tendsto this hle
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  have hslowD : ∀ x, ∀ᶠ n in atTop, ‖T n (Lf x)‖ ≤ C0 * ‖x‖ * Real.exp (n * θ) := fun x =>
    eventually_atTop.2 ⟨N, fun n hn => (hslow x n hn).trans_eq (by ring)⟩
  have hadd : ∀ x x', Lf (x + x') = Lf x + Lf x' := by
    intro x x'
    refine (huniq (x + x') (Lf x + Lf x') ?_ ⟨C0 * ‖x‖ + C0 * ‖x'‖, ?_⟩).symm
    · rw [add_sub_add_comm]; exact E.add_mem (hmem x) (hmem x')
    · filter_upwards [hslowD x, hslowD x'] with n h1 h2
      rw [map_add]; refine (norm_add_le _ _).trans ?_; linarith
  have hsmul : ∀ (c : ℝ) x, Lf (c • x) = c • Lf x := by
    intro c x
    refine (huniq (c • x) (c • Lf x) ?_ ⟨‖c‖ * (C0 * ‖x‖), ?_⟩).symm
    · rw [← smul_sub]; exact E.smul_mem c (hmem x)
    · filter_upwards [hslowD x] with n h1
      rw [map_smul, norm_smul, mul_assoc]; gcongr
  set M := 4 * Real.exp (N * (A - α)) + K * r ^ N / (1 - r) with hM
  have hbound : ∀ x, ‖Lf x‖ ≤ M * ‖x‖ := by
    intro x
    calc ‖Lf x‖ = ‖y N x - (y N x - Lf x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖y N x‖ + ‖y N x - Lf x‖ := norm_sub_le _ _
      _ ≤ 4 * Real.exp (N * (A - α)) * ‖x‖ + K * ‖x‖ * r ^ N / (1 - r) :=
          add_le_add (h.norm_le hαA le_rfl x) (htail x N le_rfl)
      _ = M * ‖x‖ := by rw [hM]; ring
  let P : X →L[ℝ] X := LinearMap.mkContinuous
    { toFun := Lf, map_add' := hadd, map_smul' := hsmul } M hbound
  exact ⟨P, hLf, hmem, ⟨C0, fun n hn x => hslow x n hn⟩, fun x z hz hD => huniq x z hz hD⟩

end Sequence

/-! ### Choosing the representatives, and the cocycle-level projection -/

/-- A rational combination of a finite family of vectors. -/
noncomputable def ratCombo {m : ℕ} (v : Fin m → X) (c : Fin m → ℚ) : X :=
  ∑ i, ((c i : ℝ)) • v i

theorem ratCombo_mem {m : ℕ} (v : Fin m → X) (c : Fin m → ℚ) :
    ratCombo v c ∈ Submodule.span ℝ (Set.range v) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Rational combinations are dense in the span: every open set meeting the span contains one. -/
theorem exists_ratCombo_mem_open {m : ℕ} (v : Fin m → X) {U : Set X} (hU : IsOpen U) {e : X}
    (he : e ∈ Submodule.span ℝ (Set.range v)) (heU : e ∈ U) :
    ∃ c : Fin m → ℚ, ratCombo v c ∈ U := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 he
  set F : (Fin m → ℝ) → X := fun a => ∑ i, a i • v i with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hd : DenseRange (Pi.map fun _ : Fin m => ((↑) : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  obtain ⟨c, hc⟩ := hd.exists_mem_open (hU.preimage hFc) ⟨a, heU⟩
  exact ⟨c, by simpa [ratCombo, hF, Pi.map] using hc⟩

open Classical in
/-- **The slow representative at one time.** `0` on `E`; otherwise `x` minus the first rational
combination `e` of the basis `v` (in the enumeration `q`) with `‖T(x-e)‖ < c‖x-e‖`. -/
noncomputable def slowSel {m : ℕ} (T : X →L[ℝ] X) (c : ℝ) (E : Submodule ℝ X) (v : Fin m → X)
    (q : ℕ → Fin m → ℚ) (x : X) : X :=
  if x ∈ E then 0 else
    x - ratCombo v (q (sInf {j | ‖T (x - ratCombo v (q j))‖ < c * ‖x - ratCombo v (q j)‖}))

theorem slowSel_spec {m : ℕ} {T : X →L[ℝ] X} {c : ℝ} {E : Submodule ℝ X} [FiniteDimensional ℝ E]
    (hm : Module.finrank ℝ E = m) {v : Fin m → X} (hv : E = Submodule.span ℝ (Set.range v))
    {q : ℕ → Fin m → ℚ} (hq : Function.Surjective q)
    (hρ : bernsteinNumber T (m + 1) < c) (hc : c ≤ growth T E) (x : X) :
    x - slowSel T c E v q x ∈ E ∧ ‖T (slowSel T c E v q x)‖ ≤ c * ‖slowSel T c E v q x‖ := by
  unfold slowSel
  split_ifs with hx
  · simp [hx]
  · set P : ℕ → Prop := fun j => ‖T (x - ratCombo v (q j))‖ < c * ‖x - ratCombo v (q j)‖ with hP
    obtain ⟨e, heE, he⟩ := exists_slow_translate hm hρ hc hx
    have hU : IsOpen {z : X | ‖T (x - z)‖ < c * ‖x - z‖} :=
      isOpen_lt (continuous_norm.comp (T.continuous.comp (continuous_const.sub continuous_id)))
        (continuous_const.mul (continuous_norm.comp (continuous_const.sub continuous_id)))
    obtain ⟨c0, hc0⟩ := exists_ratCombo_mem_open v hU (hv ▸ heE) he
    obtain ⟨j, rfl⟩ := hq c0
    have hne : {j | P j}.Nonempty := ⟨j, hc0⟩
    have hmem := Nat.sInf_mem hne
    refine ⟨?_, (hmem : P _).le⟩
    rw [sub_sub_cancel, hv]
    exact ratCombo_mem _ _

section Measurable

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]

theorem measurable_ratCombo {m : ℕ} {v : Ω → Fin m → X} (hv : ∀ i, Measurable fun ω => v ω i)
    (c : Fin m → ℚ) : Measurable fun ω => ratCombo (v ω) c :=
  Finset.measurable_sum _ fun i _ => (hv i).const_smul _

theorem measurable_slowSel {m : ℕ} {T : Ω → X →L[ℝ] X} (hT : ∀ x, Measurable fun ω => T ω x)
    {c : Ω → ℝ} (hc : Measurable c) {E : Ω → Submodule ℝ X} {v : Ω → Fin m → X}
    (hv : ∀ i, Measurable fun ω => v ω i) (q : ℕ → Fin m → ℚ) (x : X)
    (hEx : MeasurableSet {ω | x ∈ E ω}) :
    Measurable fun ω => slowSel (T ω) (c ω) (E ω) (v ω) q x := by
  classical
  set P : ℕ → Ω → Prop := fun j ω =>
    ‖T ω (x - ratCombo (v ω) (q j))‖ < c ω * ‖x - ratCombo (v ω) (q j)‖ with hPdef
  have hP : ∀ j, MeasurableSet {ω | P j ω} := fun j =>
    measurableSet_lt
      (measurable_apply_of_weak hT (measurable_const.sub (measurable_ratCombo hv _))).norm
      (hc.mul (measurable_const.sub (measurable_ratCombo hv _)).norm)
  set P' : ℕ → Ω → Prop := fun j ω => P j ω ∨ ∀ l, ¬ P l ω with hP'def
  have hP' : ∀ j, MeasurableSet {ω | P' j ω} := by
    intro j
    have hset : {ω | P' j ω} = {ω | P j ω} ∪ ⋂ l, {ω | P l ω}ᶜ := by
      ext ω; simp [hP'def]
    rw [hset]
    exact (hP j).union (MeasurableSet.iInter fun l => (hP l).compl)
  have hex : ∀ ω, ∃ j, P' j ω := by
    intro ω
    by_cases h : ∃ l, P l ω
    · obtain ⟨l, hl⟩ := h; exact ⟨l, Or.inl hl⟩
    · exact ⟨0, Or.inr fun l hl => h ⟨l, hl⟩⟩
  have hfind : ∀ ω, sInf {j | P j ω} = Nat.find (hex ω) := by
    intro ω
    by_cases h : ∃ l, P l ω
    · have hne : {j | P j ω}.Nonempty := h
      have hspec := Nat.find_spec (hex ω)
      have hk : P (Nat.find (hex ω)) ω := hspec.resolve_right fun hall => hall _ h.choose_spec
      exact le_antisymm (Nat.sInf_le hk) (Nat.find_min' (hex ω) (Or.inl (Nat.sInf_mem hne)))
    · have hset : {j | P j ω} = ∅ := Set.eq_empty_of_forall_notMem fun j hj => h ⟨j, hj⟩
      rw [hset, Nat.sInf_empty, eq_comm, Nat.find_eq_zero]
      exact Or.inr fun l hl => h ⟨l, hl⟩
  have hcomb : Measurable fun ω => ratCombo (v ω) (q (Nat.find (hex ω))) :=
    Measurable.find (f := fun j ω => ratCombo (v ω) (q j)) (fun j => measurable_ratCombo hv _)
      hP' hex
  have heq : (fun ω => slowSel (T ω) (c ω) (E ω) (v ω) q x) =
      fun ω => if ω ∈ {ω | x ∈ E ω} then 0 else x - ratCombo (v ω) (q (Nat.find (hex ω))) := by
    funext ω
    simp only [slowSel, Set.mem_ofPred_eq]
    split_ifs
    · rfl
    · congr 3
      exact hfind ω
  rw [heq]
  exact Measurable.ite hEx measurable_const (measurable_const.sub hcomb)

end Measurable

/-- **From a growth limit and an upper bound on `ρ_{m+1}` to the slow-representative
hypotheses**, with the fixed threshold `c_n = e^{nβ}` in place of `2ρ_{m+1}`. Only an *upper*
bound on `ρ_{m+1}` is used, so this works when `ρ_{m+1}` decays faster than every exponential
(`χ_{m+1} = -∞`, e.g. a finite-rank cocycle), where `2ρ_{m+1}` can be `0` and the selection
condition `‖T(x-e)‖ < 0` is unsatisfiable. -/
theorem slowRepHyp_of_bound {T S : ℕ → X →L[ℝ] X} {E : Submodule ℝ X} [FiniteDimensional ℝ E]
    {m : ℕ} (hm : Module.finrank ℝ E = m) {v : Fin m → X}
    (hv : E = Submodule.span ℝ (Set.range v)) {q : ℕ → Fin m → ℚ} (hq : Function.Surjective q)
    {lam β ε : ℝ} (hε : 0 < ε) (hgap : β + 2 * ε < lam)
    (hT : Tendsto (fun n : ℕ => logEReal ‖T n‖ / (n : EReal)) atTop (𝓝 (lam : EReal)))
    (hg : Tendsto (fun n : ℕ => logEReal (growth (T n) E) / (n : EReal)) atTop (𝓝 (lam : EReal)))
    (hρ : ∀ᶠ n : ℕ in atTop, bernsteinNumber (T n) (m + 1) < Real.exp (n * β))
    (hS : ∀ᶠ n : ℕ in atTop, ‖S n‖ ≤ Real.exp (n * ε)) :
    ∃ N, SlowRepHyp T S E (fun n => Real.exp (n * β) / 2)
      (fun n x => slowSel (T n) (Real.exp (n * β)) E v q x)
      (lam + ε) (lam - ε) β ε N := by
  have hTb := eventually_lt_exp_of_tendsto (b := lam + ε)
    (by exact_mod_cast (by linarith : lam < lam + ε)) hT
  have hgb := eventually_exp_bounds_of_tendsto (a := lam - ε) (b := lam + ε)
    (by exact_mod_cast (by linarith : lam - ε < lam))
    (by exact_mod_cast (by linarith : lam < lam + ε)) hg
  have h2 := eventually_mul_exp_le_exp (a := β) (b := lam - ε) (c := 0) (D := 2) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hTb.and (hgb.and (hρ.and (h2.and hS))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hT1, ⟨hg1, -⟩, hρ1, h21, hS1⟩ := hN n hn
  rw [zero_add] at h21
  have hexp := Real.exp_pos (n * β)
  have hg' : Real.exp (n * (lam - ε)) ≤ growth (T n) E := by rw [mul_comm]; exact hg1.le
  have h2' : 2 * Real.exp (n * β) ≤ growth (T n) E := by
    calc 2 * Real.exp (n * β) = 2 * Real.exp (β * n) := by rw [mul_comm (n : ℝ)]
      _ ≤ Real.exp ((lam - ε) * n) := h21
      _ ≤ growth (T n) E := hg1.le
  refine ⟨by rw [mul_comm]; exact hT1.le, hg', by linarith, hS1, by linarith, fun x => ?_⟩
  have hspec := slowSel_spec hm hv hq hρ1 (by linarith) x
  exact ⟨hspec.1, hspec.2.trans_eq (by ring)⟩

/-- `log max(r,1)/n → 0` gives `r_n ≤ e^{nε}` eventually, for every `ε > 0`. -/
theorem eventually_le_exp_of_tendsto_log_max {r : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => Real.log (max (r n) 1) / n) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, r n ≤ Real.exp (n * ε) := by
  filter_upwards [h.eventually_lt_const hε, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [div_lt_iff₀ hn0] at hn
  have hmax : 0 < max (r n) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have := (Real.log_lt_iff_lt_exp hmax).1 hn
  rw [mul_comm]
  exact (le_max_left _ _).trans this.le

section Cocycle

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace X]

/-- **The slow projection of a cocycle.** Given a measurable `m`-dimensional family `E` growing at
the real rate `λ` and a gap down to `χ_{m+1} = λ₂` (an `EReal`, possibly `-∞`), there is a strongly
measurable family `P ω` with `x - P ω x ∈ E(ω)`, `𝓛^{(n)}_ω ∘ P ω` growing at rate at most `b` for
every real `b > λ₂`, and a real rate `θ ∈ (λ₂, λ)` such that `P ω x` is the only point of
`x + E(ω)` growing at rate at most `θ`. -/
theorem Cocycle.exists_slowProjection (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] (m : ℕ) [NeZero m] (E : Ω → GrassmannianFin X m) (hEm : Measurable E)
    {lam : ℝ} {lam2 : EReal} (hgap : lam2 < lam)
    (hT : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal ‖R.iterate n ω‖ / (n : EReal)) atTop
      (𝓝 (lam : EReal)))
    (hg : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
      (𝓝 (lam : EReal)))
    (hρ : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (bernsteinNumber (R.iterate n ω) (m + 1)) / (n : EReal)) atTop (𝓝 lam2)) :
    ∃ (P : Ω → X →L[ℝ] X) (θ : ℝ), lam2 < θ ∧ θ < lam ∧ (∀ x, Measurable fun ω => P ω x) ∧
      ∀ᵐ ω ∂(R.μ), (∀ x, x - P ω x ∈ ((E ω).1 : Submodule ℝ X)) ∧
        (∀ b : ℝ, lam2 < b → ∃ C, ∀ᶠ n : ℕ in atTop, ∀ x,
          ‖R.iterate n ω (P ω x)‖ ≤ C * Real.exp (n * b) * ‖x‖) ∧
        (∀ x z, x - z ∈ ((E ω).1 : Submodule ℝ X) → (∃ D, ∀ᶠ n : ℕ in atTop,
          ‖R.iterate n ω z‖ ≤ D * Real.exp (n * θ)) → z = P ω x) := by
  classical
  obtain ⟨b, hbm, hbspan⟩ := measbase (X := X) m
  obtain ⟨q, hq⟩ := exists_surjective_nat (Fin m → ℚ)
  set v : Ω → Fin m → X := fun ω => b (E ω) with hvdef
  have hv : ∀ i, Measurable fun ω => v ω i := fun i =>
    (measurable_pi_apply i).comp (hbm.comp hEm)
  obtain ⟨β₀, hβ₀1, hβ₀2⟩ := EReal.lt_iff_exists_real_btwn.1 hgap
  have hβ₀lam : β₀ < lam := by exact_mod_cast hβ₀2
  set y : ℕ → X → Ω → X := fun n x ω =>
    slowSel (R.iterate n ω) (Real.exp (n * β₀)) (E ω).1 (v ω) q x with hydef
  have hEx : ∀ x : X, MeasurableSet {ω | x ∈ ((E ω).1 : Submodule ℝ X)} := by
    intro x
    have hclosed : IsClosed {V : GrassmannianFin X m | x ∈ (V.1 : Submodule ℝ X)} := by
      have hset : {V : GrassmannianFin X m | x ∈ (V.1 : Submodule ℝ X)} =
          (fun V : GrassmannianFin X m => Metric.infDist x ((V.1 : Submodule ℝ X) : Set X)) ⁻¹'
            {0} := by
        ext V
        have := V.2.1
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        exact (infDist_eq_zero_iff_mem (Submodule.closed_of_finiteDimensional _)).symm
      rw [hset]
      exact isClosed_singleton.preimage (continuous_infDist_subspace m x)
    exact hEm hclosed.measurableSet
  have hym : ∀ n x, Measurable (y n x) := fun n x =>
    measurable_slowSel (fun x => R.measurable_iterate_apply n x) measurable_const hv q x (hEx x)
  have hSt : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      Real.log (max ‖R.L (R.σ^[n] ω)‖ 1) / n) atTop (𝓝 0) := by
    have hgm : Measurable fun ω : Ω => Real.log (max ‖R.L ω‖ 1) :=
      Real.measurable_log.comp (R.measurable_norm_L.max measurable_const)
    exact L1_orbit_decay R.μ (⇑R.σ) R.ergodic.toMeasurePreserving
      (fun ω => Real.log (max ‖R.L ω‖ 1)) hgm R.forwardIntegrable
  obtain ⟨Good, hGood⟩ : ∃ Good : Ω → Prop, ∀ ω, Good ω ↔
      (Tendsto (fun n : ℕ => logEReal ‖R.iterate n ω‖ / (n : EReal)) atTop (𝓝 (lam : EReal)) ∧
      Tendsto (fun n : ℕ =>
        logEReal (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
        (𝓝 (lam : EReal)) ∧
      Tendsto (fun n : ℕ =>
        logEReal (bernsteinNumber (R.iterate n ω) (m + 1)) / (n : EReal)) atTop (𝓝 lam2) ∧
      Tendsto (fun n : ℕ => Real.log (max ‖R.L (R.σ^[n] ω)‖ 1) / n) atTop (𝓝 0)) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hae : ∀ᵐ ω ∂(R.μ), Good ω := by
    filter_upwards [hT, hg, hρ, hSt] with ω h1 h2 h3 h4 using (hGood ω).2 ⟨h1, h2, h3, h4⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = (toMeasurable R.μ {ω | ¬ Good ω})ᶜ := ⟨_, rfl⟩
  have hGm : MeasurableSet G := hGdef ▸ (measurableSet_toMeasurable _ _).compl
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    rw [hGdef] at hω
    exact by_contra fun h => hω (subset_toMeasurable _ _ h)
  have hGae : ∀ᵐ ω ∂(R.μ), ω ∈ G := by
    have h0 : R.μ {ω | ¬ Good ω} = 0 := ae_iff.1 hae
    rw [ae_iff]
    simp only [hGdef, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable, h0]
  -- the construction at a single good `ω`, for any admissible threshold `β` and `ε`
  have hpt : ∀ ω, Good ω → ∀ β ε : ℝ, lam2 < β → 0 < ε → β + 7 * ε < lam → ∃ P : X →L[ℝ] X,
      (∀ x, Tendsto (fun n => slowSel (R.iterate n ω) (Real.exp (n * β)) (E ω).1 (v ω) q x)
        atTop (𝓝 (P x))) ∧
      (∀ x, x - P x ∈ ((E ω).1 : Submodule ℝ X)) ∧
      (∃ C, ∀ᶠ n : ℕ in atTop, ∀ x,
        ‖R.iterate n ω (P x)‖ ≤ C * Real.exp (n * (β + 5 * ε)) * ‖x‖) ∧
      (∀ x z, x - z ∈ ((E ω).1 : Submodule ℝ X) → (∃ D, ∀ᶠ n : ℕ in atTop,
        ‖R.iterate n ω z‖ ≤ D * Real.exp (n * (β + 5 * ε))) → z = P x) := by
    intro ω hω β ε hβ hε hε7
    obtain ⟨h1, h2, h3, h4⟩ := (hGood ω).1 hω
    have := (E ω).2.1
    have hρb : ∀ᶠ n : ℕ in atTop, bernsteinNumber (R.iterate n ω) (m + 1) < Real.exp (n * β) :=
      (eventually_lt_exp_of_tendsto hβ h3).mono fun n hn => by rwa [mul_comm (n : ℝ)]
    obtain ⟨N, hN⟩ := slowRepHyp_of_bound (T := fun n => R.iterate n ω)
      (S := fun n => R.L (R.σ^[n] ω)) (E ω).2.2 (hbspan (E ω)) hq hε (by linarith) h1 h2 hρb
      (eventually_le_exp_of_tendsto_log_max h4 hε)
    have hθ : lam + ε + (β + (lam + ε) - 2 * (lam - ε) + ε) = β + 5 * ε := by ring
    obtain ⟨P, hlim, hmem, ⟨C, hC⟩, huniq⟩ := hN.exists_proj (fun n => rfl) hε.le (by linarith)
      (by linarith) (by linarith) (Submodule.closed_of_finiteDimensional _)
    rw [hθ] at hC huniq
    exact ⟨P, hlim, hmem, ⟨C, eventually_atTop.2 ⟨N, hC⟩⟩, huniq⟩
  set ε₀ : ℝ := (lam - β₀) / 14 with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; linarith
  have hε₀7 : β₀ + 7 * ε₀ < lam := by rw [hε₀]; linarith
  set θ : ℝ := β₀ + 5 * ε₀ with hθdef
  have hβθ : β₀ < θ := by rw [hθdef]; linarith
  have hθlam : θ < lam := by rw [hθdef]; linarith
  let P : Ω → X →L[ℝ] X := fun ω =>
    if h : ω ∈ G then Classical.choose (hpt ω (hGgood ω h) β₀ ε₀ hβ₀1 hε₀pos hε₀7) else 0
  have hPspec : ∀ ω (h : ω ∈ G),
      P ω = Classical.choose (hpt ω (hGgood ω h) β₀ ε₀ hβ₀1 hε₀pos hε₀7) :=
    fun ω h => dite_eq_left h
  refine ⟨P, θ, lt_trans hβ₀1 (by exact_mod_cast hβθ), hθlam, fun x => ?_, ?_⟩
  · refine measurable_of_tendsto_metrizable (f := fun n ω => G.indicator (y n x) ω)
      (fun n => (hym n x).indicator hGm) (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ G
    · simp only [Set.indicator_of_mem hω]
      rw [hPspec ω hω]
      exact (Classical.choose_spec (hpt ω (hGgood ω hω) β₀ ε₀ hβ₀1 hε₀pos hε₀7)).1 x
    · simp only [Set.indicator_of_notMem hω, P, dite_eq_right hω]
      exact tendsto_const_nhds
  · filter_upwards [hGae] with ω hω
    obtain ⟨-, hmem, -, huniq⟩ :=
      Classical.choose_spec (hpt ω (hGgood ω hω) β₀ ε₀ hβ₀1 hε₀pos hε₀7)
    rw [← hPspec ω hω] at hmem huniq
    rw [← hθdef] at huniq
    refine ⟨hmem, fun bb hbb => ?_, huniq⟩
    obtain ⟨β, hβ1, hβ2⟩ := EReal.lt_iff_exists_real_btwn.1
      (show lam2 < ((min bb β₀ : ℝ) : EReal) by
        rcases min_choice bb β₀ with h | h <;> rw [h] <;> assumption)
    have hβ2' : β < min bb β₀ := by exact_mod_cast hβ2
    have hβb : β < bb := lt_of_lt_of_le hβ2' (min_le_left _ _)
    have hββ₀ : β < β₀ := lt_of_lt_of_le hβ2' (min_le_right _ _)
    set ε := min ((bb - β) / 5) (min ((lam - β) / 14) ((θ - β) / 5)) with hεdef
    have hεpos : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hε1 : ε ≤ (bb - β) / 5 := min_le_left _ _
    have hε2 : ε ≤ (lam - β) / 14 := (min_le_right _ _).trans (min_le_left _ _)
    have hε3 : ε ≤ (θ - β) / 5 := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨P', -, hmem', ⟨C, hC⟩, -⟩ :=
      hpt ω (hGgood ω hω) β ε hβ1 hεpos (by linarith)
    have hmono : ∀ {r s : ℝ} {K : ℝ} (n : ℕ) (x : X), r ≤ s →
        K * Real.exp (n * r) * ‖x‖ ≤ max K 0 * Real.exp (n * s) * ‖x‖ := by
      intro r s K n x hrs
      have hx := norm_nonneg x
      have he : Real.exp (n * r) ≤ Real.exp (n * s) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hrs (Nat.cast_nonneg _))
      calc K * Real.exp (n * r) * ‖x‖ ≤ max K 0 * Real.exp (n * r) * ‖x‖ := by
            gcongr; exact le_max_left _ _
        _ ≤ max K 0 * Real.exp (n * s) * ‖x‖ := by gcongr
    have hPP : P' = P ω := by
      ext x
      refine huniq x (P' x) (hmem' x) ⟨max C 0 * ‖x‖, ?_⟩
      filter_upwards [hC] with n hn
      refine ((hn x).trans (hmono n x (show β + 5 * ε ≤ θ by linarith))).trans_eq ?_
      ring
    rw [hPP] at hC
    refine ⟨max C 0, ?_⟩
    filter_upwards [hC] with n hn x
    exact (hn x).trans (hmono n x (show β + 5 * ε ≤ bb by linarith))

end Cocycle

/-- A real exponent limit with eventual positivity is an `EReal` exponent limit. -/
theorem tendsto_logEReal_div_of_tendsto_log {u : ℕ → ℝ} {c : ℝ} (hpos : ∀ᶠ n in atTop, 0 < u n)
    (h : Tendsto (fun n : ℕ => Real.log (u n) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => logEReal (u n) / (n : EReal)) atTop (𝓝 (c : EReal)) := by
  have hc : Tendsto (fun n : ℕ => ((Real.log (u n) / n : ℝ) : EReal)) atTop (𝓝 (c : EReal)) :=
    (continuous_coe_real_ereal.tendsto c).comp h
  refine hc.congr' ?_
  filter_upwards [hpos] with n hn
  rw [logEReal_of_pos hn]
  rfl

/-- The range of an idempotent complementary to a finite-dimensional subspace is closed
complemented. -/
theorem closedComplemented_range_of_idem (P : X →L[ℝ] X) (hP : P.comp P = P) :
    (LinearMap.range (P : X →ₗ[ℝ] X)).ClosedComplemented := by
  refine ⟨P.codRestrict _ fun x => ⟨x, rfl⟩, ?_⟩
  rintro ⟨_, ⟨z, rfl⟩⟩
  ext
  simp only []
  exact congrArg (fun T : X →L[ℝ] X => T z) hP

/-- The range of an idempotent complementary to an `m`-dimensional subspace, as a point of
`𝒢^mX`. -/
noncomputable def rangeCofin {m : ℕ} (P : X →L[ℝ] X) (E : GrassmannianFin X m)
    (h : P.comp P = P ∧
      IsCompl (E.1 : Submodule ℝ X) (LinearMap.range (P : X →ₗ[ℝ] X))) :
    GrassmannianCofin X m :=
  haveI := E.2.1
  ⟨⟨LinearMap.range (P : X →ₗ[ℝ] X), closedComplemented_range_of_idem P h.1⟩,
    LinearEquiv.finiteDimensional (Submodule.quotientEquivOfIsCompl _ _ h.2.symm).symm,
    by rw [(Submodule.quotientEquivOfIsCompl _ _ h.2.symm).finrank_eq]; exact E.2.2⟩

@[simp] theorem rangeCofin_coe {m : ℕ} (P : X →L[ℝ] X) (E : GrassmannianFin X m) (h) :
    ((rangeCofin P E h).1.1 : Submodule ℝ X) = LinearMap.range (P : X →ₗ[ℝ] X) := rfl

section TopDecomp

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace X]

/-- An a.e. property holds a.e. along the whole forward orbit. -/
theorem Cocycle.ae_forall_iterate (R : Cocycle Ω X) {p : Ω → Prop} (h : ∀ᵐ ω ∂(R.μ), p ω) :
    ∀ᵐ ω ∂(R.μ), ∀ i : ℕ, p (R.σ^[i] ω) := by
  rw [ae_all_iff]
  intro i
  exact (R.ergodic.toMeasurePreserving.iterate i).quasiMeasurePreserving.ae h

/-- `log max(u, e^{-Mn})/n = max(log u / n, -M)` in `EReal`, for `u ≥ 0` and `n ≥ 1`: flooring
the operator norm at `e^{-Mn}` floors its exponent at `-M`. -/
theorem log_max_exp_div_eq {u : ℝ} (_hu : 0 ≤ u) {n : ℕ} (hn : 1 ≤ n) (M : ℝ) :
    ((Real.log (max u (Real.exp (-M * n))) / n : ℝ) : EReal) =
      max (logEReal u / (n : EReal)) ((-M : ℝ) : EReal) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_or_gt u (Real.exp (-M * n)) with h | h
  · rw [max_eq_right h, Real.log_exp, mul_div_assoc, div_self hn0.ne', mul_one,
      max_eq_right ((logEReal_div_le_iff hn (-M)).2 h)]
  · have hupos : 0 < u := lt_trans (Real.exp_pos _) h
    rw [max_eq_left h.le, logEReal_of_pos hupos]
    have hlt : -M < Real.log u / n := by
      rw [lt_div_iff₀ hn0, ← Real.exp_lt_exp, Real.exp_log hupos]; exact h
    rw [max_eq_left (by rw [coe_div_natCast]; exact_mod_cast hlt.le)]
    rfl

/-- **The norm over the window `[n, 2n]`.** If `(1/n) log‖𝓛^{(n)}_ω‖ → c` a.e. (an `EReal`, possibly
`-∞`), then for every real `b > c`, `‖𝓛^{(n)}_{σⁿω}‖ ≤ e^{nb}` eventually. This is `easyking`
(through `SubadditiveFamily.three_limits_ereal`) applied to the log-norm family floored at
`e^{-Mn}`, whose exponent is `max(c, -M)` — real, whatever `c` is. -/
theorem Cocycle.ae_eventually_norm_shift_le (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {c : EReal} (hc : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal ‖R.iterate n ω‖ / (n : EReal))
      atTop (𝓝 c)) :
    ∀ᵐ ω ∂(R.μ), ∀ b : ℝ, c < b → ∀ᶠ n : ℕ in atTop,
      ‖R.iterate n (R.σ^[n] ω)‖ ≤ Real.exp (n * b) := by
  obtain ⟨c₀, hc₀⟩ := R.exists_logProdTrunc_subadditive 1
  have hprod : ∀ n ω, R.prodBern 1 n ω = ‖R.iterate n ω‖ := by
    intro n ω
    simp [Cocycle.prodBern, bernsteinNumber_one]
  have htrunc : ∀ (M : ℕ) n ω, R.logProdTrunc 1 M n ω =
      Real.log (max ‖R.iterate n ω‖ (Real.exp (-(M : ℝ) * n))) := by
    intro M n ω
    simp only [Cocycle.logProdTrunc, hprod]
  -- for each floor `M`, the shifted limit of the floored family
  have hM : ∀ M : ℕ, ∀ᵐ ω ∂(R.μ), c < ⊤ → Tendsto (fun n : ℕ =>
      R.logProdTrunc 1 M n (R.σ^[n] ω) / n) atTop (𝓝 (max c ((-(M : ℝ) : ℝ) : EReal)).toReal) := by
    intro M
    by_cases hctop : c < ⊤
    swap
    · exact Eventually.of_forall fun ω h => absurd h hctop
    set r : ℝ := (max c ((-(M : ℝ) : ℝ) : EReal)).toReal with hrdef
    have hrc : ((r : ℝ) : EReal) = max c ((-(M : ℝ) : ℝ) : EReal) := by
      rw [hrdef]
      refine EReal.coe_toReal (max_lt hctop (EReal.coe_lt_top _)).ne ?_
      exact (lt_of_lt_of_le (EReal.bot_lt_coe _) (le_max_right _ _)).ne'
    set f : ℕ → Ω → ℝ := fun n ω => R.logProdTrunc 1 M n ω + c₀ with hfdef
    have hsub : SubadditiveFamily (⇑R.σ) f := by
      refine ⟨fun n => (R.measurable_logProdTrunc 1 M n).add_const c₀, fun m n ω => ?_⟩
      have := hc₀ M m n ω
      simp only [hfdef]
      linarith
    have h1 : Integrable (fun ω => max (f 1 ω) 0) R.μ := by
      have hbase := R.integrable_logProdTrunc_posPart 1 M
      refine Integrable.mono' (hbase.add (integrable_const |c₀|))
        (((R.measurable_logProdTrunc 1 M 1).add_const c₀).max measurable_const).aestronglyMeasurable
        ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have hA : R.logProdTrunc 1 M 1 ω ≤ max (R.logProdTrunc 1 M 1 ω) 0 := le_max_left _ _
      have hB : (0 : ℝ) ≤ max (R.logProdTrunc 1 M 1 ω) 0 := le_max_right _ _
      have hC : c₀ ≤ |c₀| := le_abs_self c₀
      have hD : (0 : ℝ) ≤ |c₀| := abs_nonneg c₀
      refine max_le ?_ ?_
      · change R.logProdTrunc 1 M 1 ω + c₀ ≤ max (R.logProdTrunc 1 M 1 ω) 0 + |c₀|
        linarith
      · exact add_nonneg hB hD
    have hfwd : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => (f n ω / n : EReal)) atTop
        (𝓝 (r : EReal)) := by
      filter_upwards [hc] with ω hω
      have hmax : Tendsto (fun n : ℕ => max (logEReal ‖R.iterate n ω‖ / (n : EReal))
          ((-(M : ℝ) : ℝ) : EReal)) atTop (𝓝 (r : EReal)) := by
        rw [hrc]; exact hω.max tendsto_const_nhds
      have htr : Tendsto (fun n : ℕ => R.logProdTrunc 1 M n ω / n) atTop (𝓝 r) := by
        refine EReal.tendsto_coe.1 (hmax.congr' ?_)
        filter_upwards [eventually_ge_atTop 1] with n hn
        rw [htrunc, log_max_exp_div_eq (norm_nonneg _) hn]
      have hsum : Tendsto (fun n : ℕ => R.logProdTrunc 1 M n ω / n + c₀ / (n : ℝ)) atTop
          (𝓝 r) := by
        simpa using htr.add (tendsto_const_div_atTop_nhds_zero_nat c₀)
      refine (EReal.tendsto_coe.2 hsum).congr' (Eventually.of_forall fun n => ?_)
      change _ = ((f n ω : ℝ) : EReal) / (n : EReal)
      rw [coe_div_natCast]
      congr 1
      simp only [hfdef]
      ring
    obtain ⟨hshift, -⟩ := SubadditiveFamily.three_limits_ereal R.ergodic hsub h1 (r : EReal) hfwd
    filter_upwards [hshift] with ω hω _hct
    have hreal : Tendsto (fun n : ℕ => f n (R.σ^[n] ω) / n) atTop (𝓝 r) :=
      EReal.tendsto_coe.1 hω
    have heq : ∀ n : ℕ, R.logProdTrunc 1 M n (R.σ^[n] ω) / n = f n (R.σ^[n] ω) / n - c₀ / n := by
      intro n; simp only [hfdef]; ring
    simp_rw [heq]
    simpa using hreal.sub (tendsto_const_div_atTop_nhds_zero_nat c₀)
  filter_upwards [ae_all_iff.2 hM] with ω hω b hb
  have hctop : c < ⊤ := lt_trans hb (EReal.coe_lt_top b)
  obtain ⟨M, hM⟩ := exists_nat_gt (-b)
  have hrb : (max c ((-(M : ℝ) : ℝ) : EReal)).toReal < b := by
    have hlt : max c ((-(M : ℝ) : ℝ) : EReal) < b :=
      max_lt hb (by exact_mod_cast (by linarith : -(M : ℝ) < b))
    have hne : max c ((-(M : ℝ) : ℝ) : EReal) ≠ ⊥ :=
      (lt_of_lt_of_le (EReal.bot_lt_coe _) (le_max_right _ _)).ne'
    rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal (max_lt hctop (EReal.coe_lt_top _)).ne hne]
    exact hlt
  filter_upwards [(hω M hctop).eventually_lt_const hrb, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [div_lt_iff₀ hn0, htrunc] at hn
  have hmaxpos : 0 < max ‖R.iterate n (R.σ^[n] ω)‖ (Real.exp (-(M : ℝ) * n)) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  rw [mul_comm (n : ℝ) b]
  exact (le_max_left _ _).trans ((Real.log_lt_iff_lt_exp hmaxpos).1 hn).le

open Classical in
/-- The generator `𝓛_ω ∘ P_ω` on `A`, `𝓛_ω` elsewhere (`proof_met.tex` l.945). -/
noncomputable def Cocycle.modL (R : Cocycle Ω X) (P : Ω → X →L[ℝ] X) (A : Set Ω) (ω : Ω) :
    X →L[ℝ] X :=
  if ω ∈ A then (R.L ω).comp (P ω) else R.L ω

theorem Cocycle.measurable_modL_apply (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {P : Ω → X →L[ℝ] X} (hPm : ∀ x, Measurable fun ω => P ω x) {A : Set Ω}
    (hA : MeasurableSet A) (x : X) : Measurable fun ω => R.modL P A ω x := by
  classical
  have heq : (fun ω => R.modL P A ω x) = fun ω => if ω ∈ A then R.L ω (P ω x) else R.L ω x := by
    funext ω
    simp only [Cocycle.modL]
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite hA (measurable_apply_of_weak R.stronglyMeasurable (hPm x))
    (R.stronglyMeasurable x)

/-- The modified cocycle is forward-integrable: on `A` its generator costs at most `log⁺ M` more. -/
theorem Cocycle.integrable_modL (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {P : Ω → X →L[ℝ] X} (hPm : ∀ x, Measurable fun ω => P ω x) {A : Set Ω}
    (hA : MeasurableSet A) {M : ℝ} (hM : ∀ ω ∈ A, ‖P ω‖ ≤ M) :
    Integrable (fun ω => Real.log (max ‖R.modL P A ω‖ 1)) R.μ := by
  have hnorm : Measurable fun ω => ‖R.modL P A ω‖ := by
    have h := measurable_bernstein_of_weak (X := X) 1 (R.measurable_modL_apply hPm hA)
    simpa only [bernsteinNumber_one] using h
  refine Integrable.mono' (R.forwardIntegrable.add (integrable_const (Real.log (max M 1))))
    (Real.measurable_log.comp (hnorm.max measurable_const)).aestronglyMeasurable ?_
  filter_upwards with ω
  have hL1 : (1 : ℝ) ≤ max ‖R.L ω‖ 1 := le_max_right _ _
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hnn : 0 ≤ Real.log (max ‖R.modL P A ω‖ 1) := Real.log_nonneg (le_max_right _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  change Real.log (max ‖R.modL P A ω‖ 1) ≤ Real.log (max ‖R.L ω‖ 1) + Real.log (max M 1)
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le ?_ ?_)
  · by_cases hω : ω ∈ A
    · simp only [Cocycle.modL, ite_eq_left hω]
      calc ‖(R.L ω).comp (P ω)‖ ≤ ‖R.L ω‖ * ‖P ω‖ := (R.L ω).opNorm_comp_le _
        _ ≤ max ‖R.L ω‖ 1 * max M 1 := by
          gcongr
          · exact le_max_left _ _
          · exact (hM ω hω).trans (le_max_left _ _)
    · simp only [Cocycle.modL, ite_eq_right hω]
      exact (le_max_left _ _).trans (le_mul_of_one_le_right (by positivity) hM1)
  · nlinarith

/-- **The modified cocycle** `𝓛'`, with generator `𝓛_ω ∘ P_ω` on `A` and `𝓛_ω` elsewhere. -/
noncomputable def Cocycle.modify (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (P : Ω → X →L[ℝ] X) (hPm : ∀ x, Measurable fun ω => P ω x) (A : Set Ω) (hA : MeasurableSet A)
    (M : ℝ) (hM : ∀ ω ∈ A, ‖P ω‖ ≤ M) : Cocycle Ω X where
  σ := R.σ
  μ := R.μ
  L := R.modL P A
  isProbability := R.isProbability
  nullSingleton := R.nullSingleton
  ergodic := R.ergodic
  stronglyMeasurable := R.measurable_modL_apply hPm hA
  forwardIntegrable := R.integrable_modL hPm hA hM

/-- **Iterates of the modified cocycle.** Along an orbit on which every `P` is idempotent and
commutes with the generator, `P` commutes with every iterate, and `𝓛'^{(n)}_ω` is `𝓛^{(n)}_ω ∘ P_ω`
as soon as the orbit segment `ω, …, σ^{n-1}ω` has visited `A`. -/
theorem Cocycle.modify_iterate (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {P : Ω → X →L[ℝ] X} (hPm : ∀ x, Measurable fun ω => P ω x) {A : Set Ω}
    (hA : MeasurableSet A) {M : ℝ} (hM : ∀ ω ∈ A, ‖P ω‖ ≤ M) (ω : Ω)
    (hidem : ∀ i : ℕ, (P (R.σ^[i] ω)).comp (P (R.σ^[i] ω)) = P (R.σ^[i] ω))
    (heq : ∀ i : ℕ, (P (R.σ^[i + 1] ω)).comp (R.L (R.σ^[i] ω)) =
      (R.L (R.σ^[i] ω)).comp (P (R.σ^[i] ω))) (n : ℕ) :
    (P (R.σ^[n] ω)).comp (R.iterate n ω) = (R.iterate n ω).comp (P ω) ∧
      (∀ i < n, R.σ^[i] ω ∈ A →
        (R.modify P hPm A hA M hM).iterate n ω = (R.iterate n ω).comp (P ω)) ∧
      ((∀ i < n, R.σ^[i] ω ∉ A) → (R.modify P hPm A hA M hM).iterate n ω = R.iterate n ω) := by
  classical
  induction n with
  | zero =>
    refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
    ext x
    simp [Cocycle.iterate]
  | succ n ih =>
    obtain ⟨hcomm, hvis, hnovis⟩ := ih
    have hstep : R.iterate (n + 1) ω = (R.L (R.σ^[n] ω)).comp (R.iterate n ω) := rfl
    have hstep' : (R.modify P hPm A hA M hM).iterate (n + 1) ω =
        (R.modL P A (R.σ^[n] ω)).comp ((R.modify P hPm A hA M hM).iterate n ω) := rfl
    have hP0 : (P ω).comp (P ω) = P ω := hidem 0
    have hcomm' : (P (R.σ^[n + 1] ω)).comp (R.iterate (n + 1) ω) =
        (R.iterate (n + 1) ω).comp (P ω) := by
      rw [hstep, ← ContinuousLinearMap.comp_assoc, heq n, ContinuousLinearMap.comp_assoc, hcomm,
        ContinuousLinearMap.comp_assoc]
    refine ⟨hcomm', fun i hi hiA => ?_, fun hno => ?_⟩
    · rw [hstep', hstep]
      by_cases hn : R.σ^[n] ω ∈ A
      · simp only [Cocycle.modL, ite_eq_left hn]
        by_cases hv : ∃ j < n, R.σ^[j] ω ∈ A
        · obtain ⟨j, hj, hjA⟩ := hv
          rw [hvis j hj hjA, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (P _),
            hcomm, ContinuousLinearMap.comp_assoc, hP0, ContinuousLinearMap.comp_assoc]
        · rw [not_exists] at hv
          rw [hnovis fun j hj hjA => hv j ⟨hj, hjA⟩, ContinuousLinearMap.comp_assoc, hcomm,
            ContinuousLinearMap.comp_assoc]
      · simp only [Cocycle.modL, ite_eq_right hn]
        have hin : i < n := by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
          · exact h
          · subst h; exact absurd hiA hn
        rw [hvis i hin hiA, ContinuousLinearMap.comp_assoc]
    · rw [hstep', hstep, hnovis fun j hj => hno j (by omega)]
      simp only [Cocycle.modL, ite_eq_right (hno n (by omega))]

/-- **Almost every orbit visits a set of positive measure in every window `[n, 2n)`**, for `n`
large: the Birkhoff averages over `[0, 2n)` and `[0, n)` both tend to `μ A > 0`, so the count in
`[n, 2n)` grows like `n μ A`. -/
theorem Cocycle.ae_eventually_visit_window (R : Cocycle Ω X) {A : Set Ω} (hA : MeasurableSet A)
    (hApos : R.μ A ≠ 0) :
    ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop, ∃ i < n, R.σ^[i] (R.σ^[n] ω) ∈ A := by
  classical
  set g : Ω → ℝ := A.indicator 1 with hgdef
  have hgm : Measurable g := measurable_const.indicator hA
  have hgi : Integrable g R.μ := (integrable_const (1 : ℝ)).indicator hA
  have hav := ae_tendsto_birkhoffAverage_of_ergodic R.ergodic g hgm hgi
  have hint : ∫ x, g x ∂(R.μ) = R.μ.real A := integral_indicator_one hA
  have hpos : 0 < R.μ.real A := ENNReal.toReal_pos hApos (measure_ne_top _ _)
  have h2top : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id
  filter_upwards [hav] with ω hω
  rw [hint] at hω
  set a := R.μ.real A with ha
  have h2 := hω.comp h2top
  filter_upwards [h2.eventually_const_lt (show 3 * a / 4 < a by linarith),
    hω.eventually_lt_const (show a < 5 * a / 4 by linarith), eventually_ge_atTop 1]
    with n h2n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  simp only [Function.comp_apply, birkhoffAverage, smul_eq_mul] at h2n hn
  rw [two_mul, birkhoffSum_add_right_apply] at h2n
  push_cast at h2n
  rw [← div_eq_inv_mul, lt_div_iff₀ (by positivity)] at h2n
  rw [← div_eq_inv_mul, div_lt_iff₀ hn0] at hn
  have hS : 0 < birkhoffSum (⇑R.σ) g n (R.σ^[n] ω) := by nlinarith
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hzero : birkhoffSum (⇑R.σ) g n (R.σ^[n] ω) = 0 := by
    unfold birkhoffSum
    refine Finset.sum_eq_zero fun i hi => ?_
    simp [hgdef, Set.indicator_of_notMem (hno i (Finset.mem_range.1 hi))]
  linarith

/-- **Temperedness of the slow projection** (`proof_met.tex` l.940--975).

The paper's argument, with its window made explicit. Over `[n, 2n]` the fast space still grows
at rate `λ₁` (from the forward limits alone, via `growth_comp_le_norm_mul`), `‖𝓛^{(n)}_{σⁿω}‖`
grows at most at rate `λ₁` (`ae_eventually_norm_shift_le`, i.e. `easyking`), and
`𝓛^{(n)}_{σⁿω} ∘ P_{σⁿω}` grows at most at rate `λ₂`. The last is the one that needs the modified
cocycle `𝓛' = 𝓛 ∘ P` on `A = {‖P‖ ≤ M}`: `𝓛'` is forward-integrable, its top exponent is `λ₂`,
and `𝓛'^{(n)}_{σⁿω} = 𝓛^{(n)}_{σⁿω} ∘ P_{σⁿω}` as soon as `[n, 2n)` meets the orbit's visits to
`A` (`modify_iterate`), which Birkhoff makes eventual (`ae_eventually_visit_window`). Writing
`x = (x - Px) + Px` then bounds `‖P_{σⁿω}‖ ≤ 3e^{4nε}`.

**Departure from `proof_met.tex`:** the paper's final estimate uses `N₂`, a growth bound for
`E(σⁿω)` over `[n, 2n]` that it asserts without proof; here it is derived from the forward
bounds at `ω` over `[0, 2n]` and `[0, n]`. Rokhlin's lemma, which the blueprint listed as a
dependency here, is not used. -/
theorem Cocycle.isTempered_slowProjection (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
     {m : ℕ} [NeZero m] {lam : ℝ} {lam2 : EReal} (hgap : lam2 < lam)
    (E : Ω → GrassmannianFin X m) (hE : R.IsFastSpace m lam E)
    (hEpos : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
      0 < growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X))
    (hnorm : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal ‖R.iterate n ω‖ / (n : EReal)) atTop
      (𝓝 (lam : EReal)))
    (P : Ω → X →L[ℝ] X) (hPm : ∀ x, Measurable fun ω => P ω x)
    (hPE : ∀ᵐ ω ∂(R.μ), ∀ x, x - P ω x ∈ ((E ω).1 : Submodule ℝ X))
    (hPidem : ∀ᵐ ω ∂(R.μ), (P ω).comp (P ω) = P ω)
    (hPeq : ∀ᵐ ω ∂(R.μ), (P (R.σ ω)).comp (R.L ω) = (R.L ω).comp (P ω))
    (hslow : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal ‖(R.iterate n ω).comp (P ω)‖ / (n : EReal)) atTop (𝓝 lam2)) :
    R.IsTempered P := by
  classical
  have hPnorm : Measurable fun ω => ‖P ω‖ := by
    have h := measurable_bernstein_of_weak (X := X) 1 hPm
    simpa only [bernsteinNumber_one] using h
  obtain ⟨M, hMpos⟩ : ∃ M : ℕ, R.μ {ω | ‖P ω‖ ≤ (M : ℝ)} ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hU : (⋃ M : ℕ, {ω | ‖P ω‖ ≤ (M : ℝ)}) = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact exists_nat_ge _
    have h0 := measure_iUnion_null h
    rw [hU, measure_univ] at h0
    exact one_ne_zero h0
  obtain ⟨A, hAdef⟩ : ∃ A : Set Ω, A = {ω | ‖P ω‖ ≤ (M : ℝ)} := ⟨_, rfl⟩
  rw [← hAdef] at hMpos
  have hA : MeasurableSet A := hAdef ▸ measurableSet_le hPnorm measurable_const
  have hMA : ∀ ω ∈ A, ‖P ω‖ ≤ (M : ℝ) := fun ω h => by rw [hAdef] at h; exact h
  -- the orbit facts
  have horb := R.ae_forall_iterate ((hPidem.and hPeq).and hPE)
  have hfacts : ∀ᵐ ω ∂(R.μ), ∀ k : ℕ,
      (∀ i : ℕ, (P (R.σ^[i] (R.σ^[k] ω))).comp (P (R.σ^[i] (R.σ^[k] ω))) =
        P (R.σ^[i] (R.σ^[k] ω))) ∧
      (∀ i : ℕ, (P (R.σ^[i + 1] (R.σ^[k] ω))).comp (R.L (R.σ^[i] (R.σ^[k] ω))) =
        (R.L (R.σ^[i] (R.σ^[k] ω))).comp (P (R.σ^[i] (R.σ^[k] ω)))) := by
    filter_upwards [horb] with ω ho k
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [← Function.iterate_add_apply]; exact (ho (i + k)).1.1
    · rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        show i + 1 + k = (i + k) + 1 by omega, Function.iterate_succ_apply']
      exact (ho (i + k)).1.2
  -- the modified cocycle has top exponent `λ₂`
  have hvisit := ae_exists_mem_iterate R.ergodic hA hMpos
  have hR' : ∀ᵐ ω ∂((R.modify P hPm A hA M hMA).μ), Tendsto (fun n : ℕ =>
      logEReal ‖(R.modify P hPm A hA M hMA).iterate n ω‖ / (n : EReal)) atTop
      (𝓝 lam2) := by
    change ∀ᵐ ω ∂(R.μ), _
    filter_upwards [hfacts, hvisit, hslow] with ω hf hv hs
    obtain ⟨i, hi⟩ := hv
    obtain ⟨hid, heq⟩ := hf 0
    simp only [Function.iterate_zero_apply] at hid heq
    refine hs.congr' ?_
    filter_upwards [eventually_gt_atTop i] with n hn
    rw [(R.modify_iterate hPm hA hMA ω hid heq n).2.1 i hn hi]
  have hshiftR := R.ae_eventually_norm_shift_le hnorm
  have hshiftR' := (R.modify P hPm A hA M hMA).ae_eventually_norm_shift_le hR'
  have hwin := R.ae_eventually_visit_window hA hMpos
  have hEeq := R.ae_all_shift_equivariant E hE.2.2.1
  filter_upwards [horb, hfacts, hwin, hshiftR, hshiftR', hEeq, hE.2.2.2, hEpos, hnorm]
    with ω ho hf hw hsR hsR' hEq hg hgp hnω
  have hgE := tendsto_logEReal_div_of_tendsto_log hgp hg
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn1
    have hnn : 0 ≤ Real.log ‖P (R.σ^[n] ω)‖ := by
      by_cases h0 : P (R.σ^[n] ω) = 0
      · simp [h0]
      · exact Real.log_nonneg (one_le_norm_of_isIdempotent (ho n).1.1 h0)
    exact lt_of_lt_of_le ha (div_nonneg hnn (Nat.cast_nonneg _))
  · set ε := b / 8 with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; linarith
    have h2top : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id
    have hg2 := (eventually_exp_bounds_of_tendsto (a := lam - ε) (b := lam + ε)
      (by exact_mod_cast (by linarith : lam - ε < lam))
      (by exact_mod_cast (by linarith : lam < lam + ε)) hgE)
    have hg2' := h2top.eventually hg2
    have hTn := eventually_lt_exp_of_tendsto (b := lam + ε)
      (by exact_mod_cast (by linarith : lam < lam + ε)) hnω
    have hlog3 : Tendsto (fun n : ℕ => Real.log 3 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hg2', hTn, hsR (lam + ε) (by exact_mod_cast (by linarith : lam < lam + ε)),
      hsR' (lam + ε) (lt_trans hgap (by exact_mod_cast (by linarith : lam < lam + ε))), hw,
      hlog3.eventually_lt_const (show (0 : ℝ) < b / 2 by linarith), eventually_ge_atTop 1]
      with n hgn hTnω hsRn hsR'n hwn hl3 hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    set ω' := R.σ^[n] ω with hω'
    set T := R.iterate n ω' with hTdef
    -- (i) the slow part over the window
    have hTP : ‖T.comp (P ω')‖ ≤ Real.exp (n * (lam + ε)) := by
      obtain ⟨hid, heq⟩ := hf n
      obtain ⟨i, hi, hiA⟩ := hwn
      rw [hTdef, ← (R.modify_iterate hPm hA hMA ω' hid heq n).2.1 i hi hiA]
      exact hsR'n
    -- (iii) the fast space is still fast over the window
    have hgrow : Real.exp ((lam - 3 * ε) * n) ≤ growth T ((E ω').1 : Submodule ℝ X) := by
      have hcomp := growth_comp_le_norm_mul (R.iterate n ω) T ((E ω).1 : Submodule ℝ X)
      rw [← R.iterate_add n n ω, R.map_iterate_of_equivariant E ω hEq n,
        show n + n = 2 * n by ring] at hcomp
      have hle : Real.exp ((lam - ε) * (2 * n : ℕ)) ≤
          Real.exp ((lam + ε) * n) * growth T ((E ω').1 : Submodule ℝ X) := by
        refine hgn.1.le.trans (hcomp.trans ?_)
        exact mul_le_mul_of_nonneg_right hTnω.le (growth_nonneg _ _)
      have hsplit : Real.exp ((lam - ε) * (2 * n : ℕ)) =
          Real.exp ((lam + ε) * n) * Real.exp ((lam - 3 * ε) * n) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [hsplit] at hle
      exact le_of_mul_le_mul_left hle (Real.exp_pos _)
    -- (iv) the fast component of every vector is small
    have hPx : ∀ x, ‖P ω' x‖ ≤ 3 * Real.exp (4 * ε * n) * ‖x‖ := by
      intro x
      have he := (ho n).2 x
      have hx := norm_nonneg x
      have h1 : Real.exp ((lam - 3 * ε) * n) * ‖x - P ω' x‖ ≤
          2 * Real.exp (n * (lam + ε)) * ‖x‖ := by
        calc Real.exp ((lam - 3 * ε) * n) * ‖x - P ω' x‖
            ≤ growth T ((E ω').1 : Submodule ℝ X) * ‖x - P ω' x‖ := by gcongr
          _ ≤ ‖T (x - P ω' x)‖ := growth_mul_norm_le T he
          _ ≤ ‖T x‖ + ‖T.comp (P ω') x‖ := by rw [map_sub]; exact norm_sub_le _ _
          _ ≤ ‖T‖ * ‖x‖ + ‖T.comp (P ω')‖ * ‖x‖ :=
              add_le_add (T.le_opNorm x) ((T.comp (P ω')).le_opNorm x)
          _ ≤ Real.exp (n * (lam + ε)) * ‖x‖ + Real.exp (n * (lam + ε)) * ‖x‖ := by
              gcongr
          _ = 2 * Real.exp (n * (lam + ε)) * ‖x‖ := by ring
      have hsplit : Real.exp (n * (lam + ε)) =
          Real.exp ((lam - 3 * ε) * n) * Real.exp (4 * ε * n) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit] at h1
      have h2 : ‖x - P ω' x‖ ≤ 2 * Real.exp (4 * ε * n) * ‖x‖ := by
        refine le_of_mul_le_mul_left ?_ (Real.exp_pos ((lam - 3 * ε) * n))
        nlinarith
      have hone : 1 ≤ Real.exp (4 * ε * n) := Real.one_le_exp (by positivity)
      calc ‖P ω' x‖ = ‖x - (x - P ω' x)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - P ω' x‖ := norm_sub_le _ _
        _ ≤ 3 * Real.exp (4 * ε * n) * ‖x‖ := by nlinarith
    have hPn : ‖P ω'‖ ≤ 3 * Real.exp (4 * ε * n) :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) hPx
    -- (vi) the exponent
    rw [div_lt_iff₀ hn0]
    by_cases h0 : P ω' = 0
    · simp only [h0, norm_zero, Real.log_zero]; positivity
    · have hpos : 0 < ‖P ω'‖ := norm_pos_iff.2 h0
      have hlog : Real.log ‖P ω'‖ ≤ Real.log 3 + 4 * ε * n := by
        calc Real.log ‖P ω'‖ ≤ Real.log (3 * Real.exp (4 * ε * n)) := Real.log_le_log hpos hPn
          _ = Real.log 3 + 4 * ε * n := by
            rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      rw [div_lt_iff₀ hn0] at hl3
      rw [hεdef] at hlog
      nlinarith

/-- **Lemma \ref{topdecomp}.** A quasicompact, semi-invertible cocycle admits a
forward-equivariant decomposition `X = E(ω) ⊕ V(ω)` with `V` slow-growing at rate `λ₂` and a
tempered, strongly measurable projection `P`.

**Four corrections to the statement, three of them the same defect class as `Tbiggrow`.**

1. `m₁` was an input. It occurred only in the conclusion, so the statement claimed a fast space
   of *every* dimension. It is now produced, as `Cocycle.mult 0`, exactly as in
   `Cocycle.exists_topFastSpace`.
2. `k` was an input too, and the slow space `V : Ω → 𝒢^kX` was asserted to exist in every
   codimension. `V` is the complement of `E`, so its codimension is `m₁`.
3. **The decomposition was not asserted at all.** `E` and `V` appeared in the conclusion with no
   relation between them: nothing said `X = E(ω) ⊕ V(ω)`, which is the whole content of the
   lemma's name. The `IsCompl` clause is now there, as is equivariance of `V`, and — needed
   for `Cocycle.V_characterisation`, which nothing else links `P` to `V` for — that `P ω` is
   the projection onto `V ω` along `E ω`.
4. `Measurable P` was *norm* measurability of the operator family. `𝓑(X)` is not separable, so
   that is strictly stronger than what the paper says ("strongly measurable") and than what the
   construction gives — `P ω` is built as a pointwise limit, so only `ω ↦ P ω x` is measurable
   for each fixed `x`. See `ProofMet/StrongMeasurability.lean` for why the distinction matters.

**Proof.** `Cocycle.exists_slowProjection` builds `P` from `Cocycle.exists_topFastSpace_pos`; the
projection identities, the complement and equivariance all follow from its uniqueness clause
(`P ω x` is the only point of `x + E(ω)` growing below the midpoint of the gap), and the rate
`λ₂` is squeezed between that construction's upper bound and `ρ_{m₁+1}(𝓛^{(n)}_ω) ≤ ‖𝓛^{(n)}_ω P_ω‖`
(`Tsmallgrow`). Temperedness is `Cocycle.isTempered_slowProjection`.

**The paper's three gaps** (`human/errata.tex` E16--E18) do not arise on this route: `ι_n` need
only be finite past the threshold, since `slowSel` is a slow representative only where the rate
estimates already hold; measurability is taken for each fixed `x` separately
(`measurable_slowSel`); and temperedness does not need `lem:rokhlin` after all. -/
theorem Cocycle.topdecomp (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] [CompleteSpace X]
    (hqc : R.IsQuasicompact)
    (lam : ℝ) (lam2 : EReal) (hlam : ∀ᵐ ω ∂(R.μ), R.chi 1 ω = (lam : EReal))
    (hlam2 : ∀ᵐ ω ∂(R.μ), R.lambda 1 ω = lam2) :
    ∃ (m1 : ℕ) (_ : NeZero m1) (E : Ω → GrassmannianFin X m1)
      (V : Ω → GrassmannianCofin X m1) (P : Ω → X →L[ℝ] X),
      (∀ᵐ ω ∂(R.μ), R.mult 0 ω = m1) ∧
      R.IsFastSpace m1 lam E ∧
      (∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        0 < growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) ∧
      (∀ x : X, Measurable fun ω => P ω x) ∧
      (∀ᵐ ω ∂(R.μ), (P ω).comp (P ω) = P ω) ∧
      (∀ᵐ ω ∂(R.μ), IsCompl ((E ω).1 : Submodule ℝ X) ((V ω).1.1 : Submodule ℝ X)) ∧
      (∀ᵐ ω ∂(R.μ), LinearMap.range (P ω : X →ₗ[ℝ] X) = ((V ω).1.1 : Submodule ℝ X) ∧
        ∀ e ∈ ((E ω).1 : Submodule ℝ X), P ω e = 0) ∧
      (∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((V ω).1.1 : Submodule ℝ X)
          ≤ ((V (R.σ ω)).1.1 : Submodule ℝ X)) ∧
      R.IsTempered P ∧
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
        logEReal ‖(R.iterate n ω).comp (P ω)‖ / (n : EReal)) atTop (nhds lam2)) := by
  classical
  obtain ⟨m1, hm1, E, hmult, hE, hEpos⟩ := R.exists_topFastSpace_pos hqc lam hlam
  have hm1pos : 0 < m1 := Nat.pos_of_ne_zero (NeZero.ne m1)
  have hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m1 + 1) ω = lam2 := by
    filter_upwards [hmult, hlam2] with ω hm hl
    have hidx : R.lambdaIdx 1 ω = m1 + 1 := by
      have h0 : R.lambdaIdx 0 ω = 1 := rfl
      have h1 : R.mult 0 ω = R.lambdaIdx 1 ω - R.lambdaIdx 0 ω := rfl
      omega
    rw [← hl]
    change _ = R.chi (R.lambdaIdx 1 ω) ω
    rw [hidx]
  have hgap : lam2 < lam := by
    obtain ⟨ω, hm, h2, h1⟩ := (hmult.and (hchi2.and hlam)).exists
    have := R.chi_mult_succ_lt ω (by rw [hm]; exact hm1pos)
    rwa [hm, h2, h1] at this
  have hT : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal ‖R.iterate n ω‖ / (n : EReal)) atTop
      (𝓝 (lam : EReal)) := by
    filter_upwards [R.ae_tendsto_chi 1, hlam] with ω h hl
    rw [hl] at h
    simpa only [bernsteinNumber_one] using h
  have hg : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
      (𝓝 (lam : EReal)) := by
    filter_upwards [hE.2.2.2, hEpos] with ω h hp using tendsto_logEReal_div_of_tendsto_log hp h
  have hρ : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (bernsteinNumber (R.iterate n ω) (m1 + 1)) / (n : EReal)) atTop
      (𝓝 lam2) := by
    filter_upwards [R.ae_tendsto_chi (m1 + 1), hchi2] with ω h hc
    rwa [hc] at h
  obtain ⟨P, θ, hθ1, -, hPm, hP⟩ := R.exists_slowProjection m1 E hE.1 hgap hT hg hρ
  -- the algebra of `P ω` at a good point
  have hfacts : ∀ᵐ ω ∂(R.μ), (∀ e ∈ ((E ω).1 : Submodule ℝ X), P ω e = 0) ∧
      (P ω).comp (P ω) = P ω ∧
      IsCompl ((E ω).1 : Submodule ℝ X) (LinearMap.range (P ω : X →ₗ[ℝ] X)) := by
    filter_upwards [hP] with ω hω
    obtain ⟨hmem, hslow, huniq⟩ := hω
    obtain ⟨C, hC⟩ := hslow θ hθ1
    have hzero : ∀ e ∈ ((E ω).1 : Submodule ℝ X), P ω e = 0 := fun e he =>
      (huniq e 0 (by simpa using he) ⟨0, Eventually.of_forall fun n => by simp⟩).symm
    have hidem : ∀ x, P ω (P ω x) = P ω x := fun x =>
      (huniq (P ω x) (P ω x) (by simp)
        ⟨C * ‖x‖, hC.mono fun n hn => (hn x).trans_eq (by ring)⟩).symm
    refine ⟨hzero, ContinuousLinearMap.ext hidem, ?_⟩
    constructor
    · rw [Submodule.disjoint_def]
      rintro e he ⟨z, rfl⟩
      have h1 := hzero _ he
      simp only [ContinuousLinearMap.coe_coe] at h1 ⊢
      rwa [hidem] at h1
    · rw [codisjoint_iff, eq_top_iff]
      rintro x -
      exact Submodule.mem_sup.2 ⟨x - P ω x, hmem x, P ω x, ⟨x, rfl⟩, sub_add_cancel _ _⟩
  have hne : Nonempty (GrassmannianCofin X m1) := by
    obtain ⟨ω, -, hid, hc⟩ := hfacts.exists
    exact ⟨rangeCofin (P ω) (E ω) ⟨hid, hc⟩⟩
  let V : Ω → GrassmannianCofin X m1 := fun ω =>
    if h : (P ω).comp (P ω) = P ω ∧
        IsCompl ((E ω).1 : Submodule ℝ X) (LinearMap.range (P ω : X →ₗ[ℝ] X))
    then rangeCofin (P ω) (E ω) h else Classical.choice hne
  have hV : ∀ᵐ ω ∂(R.μ), ((V ω).1.1 : Submodule ℝ X) = LinearMap.range (P ω : X →ₗ[ℝ] X) := by
    filter_upwards [hfacts] with ω hω
    simp only [V, dite_eq_left (show _ ∧ _ from ⟨hω.2.1, hω.2.2⟩), rangeCofin_coe]
  have hmp := R.ergodic.toMeasurePreserving
  have hPσ := hmp.quasiMeasurePreserving.ae hP
  have hVσ := hmp.quasiMeasurePreserving.ae hV
  have hfactsσ := hmp.quasiMeasurePreserving.ae hfacts
  -- equivariance of the slow space
  have hequiv : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X)
      (LinearMap.range (P ω : X →ₗ[ℝ] X)) ≤ LinearMap.range (P (R.σ ω) : X →ₗ[ℝ] X) := by
    filter_upwards [hP, hPσ] with ω hω hωσ
    obtain ⟨-, hslow, -⟩ := hω
    obtain ⟨-, -, huniqσ⟩ := hωσ
    obtain ⟨C, hC⟩ := hslow θ hθ1
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨R.L ω (P ω z), ?_⟩
    simp only [ContinuousLinearMap.coe_coe]
    refine (huniqσ _ _ (by simp) ⟨C * ‖z‖ * Real.exp θ, ?_⟩).symm
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hC] with n hn
    have h1 := hn z
    rw [R.iterate_succ_left] at h1
    refine h1.trans_eq ?_
    push_cast
    rw [add_mul, one_mul, Real.exp_add]
    ring
  have hrate : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal ‖(R.iterate n ω).comp (P ω)‖ / (n : EReal)) atTop (𝓝 lam2) := by
    filter_upwards [hP, hfacts, hρ] with ω hω hf hρω
    obtain ⟨-, hslow, -⟩ := hω
    refine tendsto_order.2 ⟨fun a ha => ?_, fun c hc => ?_⟩
    · filter_upwards [hρω.eventually_const_lt ha] with n hn
      refine lt_of_lt_of_le hn (EReal.div_le_div_right_of_nonneg (by positivity)
        (ChiOrder.logEReal_mono ?_))
      have hsmall := Tsmallgrow m1 1 one_ne_zero (rangeCofin (P ω) (E ω) ⟨hf.2.1, hf.2.2⟩)
        (P ω) (fun x => ⟨x, rfl⟩) (by
          rintro _ ⟨z, rfl⟩
          simp only [ContinuousLinearMap.coe_coe]
          exact congrArg (fun T : X →L[ℝ] X => T z) hf.2.1) (R.iterate n ω)
      rwa [bernsteinNumber_one] at hsmall
    · obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
      obtain ⟨b', hb'1, hb'2⟩ := EReal.lt_iff_exists_real_btwn.1 hb2
      have hbb' : b < b' := by exact_mod_cast hb'1
      obtain ⟨C, hC⟩ := hslow b hb1
      filter_upwards [hC, eventually_mul_exp_le_exp (a := b) (b := b') (c := 0) (D := max C 0)
        hbb', eventually_ge_atTop 1] with n hn hD hn1
      rw [zero_add] at hD
      refine lt_of_le_of_lt ((logEReal_div_le_iff hn1 b').2 ?_) hb'2
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x => ?_
      refine (hn x).trans ?_
      have hx := norm_nonneg x
      calc C * Real.exp (n * b) * ‖x‖ ≤ max C 0 * Real.exp (b * n) * ‖x‖ := by
            rw [mul_comm (n : ℝ) b]; gcongr; exact le_max_left _ _
        _ ≤ Real.exp (b' * n) * ‖x‖ := by gcongr
  refine ⟨m1, hm1, E, V, P, hmult, hE, hEpos, hPm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hfacts] with ω h using h.2.1
  · filter_upwards [hfacts, hV] with ω h hVω
    rw [hVω]; exact h.2.2
  · filter_upwards [hfacts, hV] with ω h hVω using ⟨hVω.symm, h.1⟩
  · filter_upwards [hequiv, hV, hVσ] with ω h hVω hVσω
    rw [hVω, hVσω]; exact h
  · refine R.isTempered_slowProjection hgap E hE hEpos hT P hPm ?_ ?_ ?_ ?_
    · filter_upwards [hP] with ω h using h.1
    · filter_upwards [hfacts] with ω h using h.2.1
    · filter_upwards [hP, hfacts, hfactsσ, hequiv, hE.2.2.1] with ω hω hf hfσ heq hEeq
      ext x
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
      have hdecomp : x = (x - P ω x) + P ω x := (sub_add_cancel _ _).symm
      have hE1 : R.L ω (x - P ω x) ∈ ((E (R.σ ω)).1 : Submodule ℝ X) := by
        rw [← hEeq]; exact Submodule.mem_map_of_mem (hω.1 x)
      have hV1 : R.L ω (P ω x) ∈ LinearMap.range (P (R.σ ω) : X →ₗ[ℝ] X) :=
        heq (Submodule.mem_map_of_mem ⟨x, rfl⟩)
      obtain ⟨w, hw⟩ := hV1
      simp only [ContinuousLinearMap.coe_coe] at hw
      conv_lhs => rw [hdecomp, map_add, map_add, hfσ.1 _ hE1, zero_add, ← hw]
      rw [← ContinuousLinearMap.comp_apply, hfσ.2.1, hw]
    · exact hrate
  · exact hrate


/-- An eventual exponential bound caps the growth rate of a vector. -/
theorem Cocycle.lambdaAt_le_of_eventually_le (R : Cocycle Ω X) {ω : Ω} {x : X} {K c : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, ‖R.iterate n ω x‖ ≤ K * Real.exp (n * c)) :
    R.lambdaAt ω x ≤ (c : EReal) := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨M, hcM, hMlt⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hcM' : c < M := by exact_mod_cast hcM
  have hev : ∀ᶠ n : ℕ in atTop, logEReal ‖R.iterate n ω x‖ / (n : EReal) ≤ (M : EReal) := by
    filter_upwards [h, eventually_mul_exp_le_exp (a := c) (b := M) (c := 0) (D := K) hcM',
      eventually_ge_atTop 1] with n hn hK hn1
    rw [zero_add] at hK
    refine (logEReal_div_le_iff hn1 M).2 (hn.trans ?_)
    rw [mul_comm (n : ℝ) c] at hn ⊢
    exact hK
  have hle : R.lambdaAt ω x ≤ (M : EReal) :=
    (limsup_le_limsup hev).trans (limsup_const _).le
  exact absurd hle (not_le.2 hMlt)

/-- A growth rate below `c` gives an eventual exponential bound at rate `c`. -/
theorem Cocycle.eventually_lt_exp_of_lambdaAt_lt (R : Cocycle Ω X) {ω : Ω} {x : X} {c : ℝ}
    (h : R.lambdaAt ω x < (c : EReal)) :
    ∀ᶠ n : ℕ in atTop, ‖R.iterate n ω x‖ < Real.exp (c * n) := by
  filter_upwards [eventually_lt_of_limsup_lt h, eventually_ge_atTop 1] with n hn hn1
  exact (logEReal_div_lt_iff hn1 c).1 hn

/-- **Corollary \ref{cor:V-characterisation}.** In the setting of `Cocycle.topdecomp`, the slow
space is exactly the set of vectors growing at rate at most `λ₂`:
`V(ω) = {x : λ_ω(x) ≤ λ₂}` almost surely.

The hypotheses are the conclusions of `Cocycle.topdecomp` that the argument uses, so the
corollary applies to any decomposition of that shape: `E` a fast space at rate `λ`, `P ω` the
projection onto `V ω` along `E ω`, and `𝓛^{(n)}_ω ∘ P ω` growing at rate `λ₂ < λ`.

`⊆` is the slow bound `‖𝓛^{(n)}_ω x‖ ≤ ‖𝓛^{(n)}_ω P_ω‖‖x‖` for `x = P_ω x`. `⊇`: the fast component
`x - P_ω x ∈ E(ω)` is then slow too, but every nonzero vector of `E(ω)` grows at rate `λ`. -/
theorem Cocycle.V_characterisation (R : Cocycle Ω X) {m : ℕ} [NeZero m] {lam : ℝ}
    {lam2 : EReal} (hgap : lam2 < lam) (E : Ω → GrassmannianFin X m) (hE : R.IsFastSpace m lam E)
    (V : Ω → GrassmannianCofin X m) (P : Ω → X →L[ℝ] X)
    (hidem : ∀ᵐ ω ∂(R.μ), (P ω).comp (P ω) = P ω)
    (hcompl : ∀ᵐ ω ∂(R.μ), IsCompl ((E ω).1 : Submodule ℝ X) ((V ω).1.1 : Submodule ℝ X))
    (hPV : ∀ᵐ ω ∂(R.μ), LinearMap.range (P ω : X →ₗ[ℝ] X) = ((V ω).1.1 : Submodule ℝ X) ∧
      ∀ e ∈ ((E ω).1 : Submodule ℝ X), P ω e = 0)
    (hslow : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal ‖(R.iterate n ω).comp (P ω)‖ / (n : EReal)) atTop (𝓝 lam2)) :
    ∀ᵐ ω ∂(R.μ), (((V ω).1.1 : Submodule ℝ X) : Set X) = {x : X | R.lambdaAt ω x ≤ lam2} := by
  filter_upwards [hE.2.1, hidem, hcompl, hPV, hslow] with ω hElam hid hc hPVω hs
  obtain ⟨hrange, hker⟩ := hPVω
  have hfix : ∀ v ∈ ((V ω).1.1 : Submodule ℝ X), P ω v = v := by
    intro v hv
    rw [← hrange] at hv
    obtain ⟨z, rfl⟩ := hv
    exact congrArg (fun T : X →L[ℝ] X => T z) hid
  have hfast : ∀ x, x - P ω x ∈ ((E ω).1 : Submodule ℝ X) := by
    intro x
    have hx : x ∈ ((E ω).1 : Submodule ℝ X) ⊔ ((V ω).1.1 : Submodule ℝ X) := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hker a ha, hfix b hb, zero_add, add_sub_cancel_right]
    exact ha
  -- the slow bound on `𝓛^{(n)}_ω ∘ P_ω`, at every rate above `λ₂`
  have hPbound : ∀ M : ℝ, lam2 < (M : EReal) → ∀ x, ∀ᶠ n : ℕ in atTop,
      ‖R.iterate n ω (P ω x)‖ ≤ ‖x‖ * Real.exp (n * M) := by
    intro M hM x
    filter_upwards [eventually_lt_exp_of_tendsto hM hs] with n hn
    calc ‖R.iterate n ω (P ω x)‖ = ‖(R.iterate n ω).comp (P ω) x‖ := rfl
      _ ≤ ‖(R.iterate n ω).comp (P ω)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.exp (n * M) * ‖x‖ := by rw [mul_comm (n : ℝ)]; gcongr
      _ = ‖x‖ * Real.exp (n * M) := mul_comm _ _
  ext x
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  constructor
  · intro hx
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨M, hM, hM2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hle : R.lambdaAt ω x ≤ (M : EReal) := by
      refine R.lambdaAt_le_of_eventually_le (K := ‖x‖) ?_
      filter_upwards [hPbound M hM x] with n hn
      rwa [hfix x hx] at hn
    exact absurd hle (not_le.2 hM2)
  · intro hx
    obtain ⟨c, hc2, hclam'⟩ := EReal.lt_iff_exists_real_btwn.1 hgap
    have hclam : c < lam := by exact_mod_cast hclam'
    have hxlt : R.lambdaAt ω x < (c : EReal) := lt_of_le_of_lt hx hc2
    have he : x - P ω x = 0 := by
      by_contra he0
      have hlam := hElam _ (hfast x) he0
      have hle : R.lambdaAt ω (x - P ω x) ≤ (c : EReal) := by
        refine R.lambdaAt_le_of_eventually_le (K := 1 + ‖x‖) ?_
        filter_upwards [R.eventually_lt_exp_of_lambdaAt_lt hxlt, hPbound c hc2 x] with n h1 h2
        rw [map_sub]
        refine (norm_sub_le _ _).trans ?_
        rw [mul_comm c] at h1
        nlinarith [Real.exp_pos (n * c)]
      rw [hlam] at hle
      exact absurd (show lam ≤ c by exact_mod_cast hle) (not_le.2 hclam)
    have hmem : x ∈ LinearMap.range (P ω : X →ₗ[ℝ] X) := ⟨x, (sub_eq_zero.1 he).symm⟩
    rwa [hrange] at hmem

end TopDecomp

end MultiplicativeErgodic
