/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Extended-real potentials and the Legendre transform

For `φ : E → EReal` on a real inner product space, `legendre φ y = ⨆ x, ⟪x, y⟫ - φ x` is the actual
extended-real
Legendre transform, with no selected maximizers. `ConvexPotential φ` excludes `-∞` and asks for a
convex real epigraph;
`ProperPotential φ` excludes `-∞` and asks for one finite value.

* Order reversal `legendre_antitone`; exclusion of `-∞` (`legendre_ne_bot`, and
  `legendre_ne_bot_iff`: exactly a nonempty
  effective domain); the Fenchel inequality `fenchel_le`, `biconjugate_le` and `triconjugate_eq`. No
  convexity of the
  primal is assumed.
* For every input, `lowerSemicontinuous_legendre` and `convex_epigraph_legendre`;
  `convexPotential_legendre` from a
  nonempty effective domain.
* A convex potential has a convex effective domain `{φ ≠ ⊤}` (`ConvexPotential.convex_domain`) on
  which its real
  representative `(φ ·).toReal` is convex (`ConvexPotential.convexOn_toReal`).
* The lower truncation `lowerTruncate φ M = max φ (-M)` of Cordero-Erausquin–Klartag, *Moment
  measures*
  (arXiv:1304.0630v1), (61), and its convexification `lowerTruncate_convexification` (proof of
  Proposition 12): the
  biconjugate is a convex, lower semicontinuous proper potential between `-M` and the truncation,
  with the same transform.
* `legendre_eq_interior_sup`: if `K` is open and convex with `0 ∈ K`, and `ψ` is radially closed and
  `⊤` off `closure K`,
  the transform is the supremum of its affine terms over `K` (proof of Lemma 17, (56b)).

Measure-free; the exponential density, mass and the CEK functional are in
`Probability/MomentMeasure/`.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Convexity of an extended-real potential, expressed through its real epigraph. -/
def ConvexPotential (φ : E → EReal) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}

/-- The actual extended-real Legendre transform; no selected maximizers are assumed. -/
def legendre (φ : E → EReal) (y : E) : EReal :=
  ⨆ x : E, (inner ℝ x y : EReal) - φ x

/-- A finite-value witness as well as exclusion of `-∞`, rather than a desired conclusion. -/
def ProperPotential (φ : E → EReal) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ ∃ x, φ x ≠ ⊤

/-- The Legendre transform reverses pointwise order, including extended values. -/
theorem legendre_antitone {φ ψ : E → EReal} (h : ∀ x, φ x ≤ ψ x) (y : E) :
    legendre ψ y ≤ legendre φ y := by
  apply iSup_le
  intro x
  exact (EReal.sub_le_sub le_rfl (h x)).trans
    (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)

/-- One finite value excludes `-∞` for the entire Legendre transform. -/
theorem legendre_ne_bot (φ : E → EReal) (hφ : ProperPotential φ) (y : E) :
    legendre φ y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hφ.2
  have hb := hφ.1 x
  lift φ x to ℝ using ⟨hx, hb⟩ with r hr
  have hle : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
    change ((inner ℝ x y - r : ℝ) : EReal) ≤
      ⨆ z : E, (inner ℝ z y : EReal) - φ z
    simpa only [← hr, EReal.coe_sub] using
      (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hle)

/-- Fenchel inequality for a proper extended potential; no convexity is assumed. -/
theorem fenchel_le (φ : E → EReal) (hφ : ProperPotential φ) (x y : E) :
    (inner ℝ x y : EReal) ≤ φ x + legendre φ y := by
  have h := le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x
  have hi := (EReal.sub_le_iff_le_add (.inl (hφ.1 x))
    (.inr (legendre_ne_bot φ hφ y))).mp h
  simpa only [add_comm] using hi

/-- The biconjugate never exceeds a proper extended potential. -/
theorem biconjugate_le (φ : E → EReal) (hφ : ProperPotential φ) (x : E) :
    legendre (legendre φ) x ≤ φ x := by
  apply iSup_le
  intro y
  exact EReal.sub_le_of_le_add (by
    simpa only [real_inner_comm] using fenchel_le φ hφ x y)

/-- A real lower bound on the primal gives a finite upper bound for its
Legendre transform at zero. This is the normalization used after CEK (61). -/
theorem legendre_zero_le_of_lower_bound (φ : E → EReal) (M : ℝ)
    (h : ∀ x, ((-M : ℝ) : EReal) ≤ φ x) : legendre φ 0 ≤ (M : EReal) := by
  apply iSup_le
  intro x
  simp only [inner_zero_right, EReal.coe_zero, zero_sub]
  apply EReal.neg_le.mpr
  simpa only [EReal.coe_neg] using h x

/-- For proper primal and dual potentials, convexification does not alter the
Legendre transform. This is the identity used for `φ_ℓ = (g_ℓ*)*` in Proposition 12. -/
theorem triconjugate_eq (φ : E → EReal) (hφ : ProperPotential φ)
    (hdual : ProperPotential (legendre φ)) (y : E) :
    legendre (legendre (legendre φ)) y = legendre φ y := by
  apply le_antisymm
  · exact biconjugate_le (legendre φ) hdual y
  · exact legendre_antitone (biconjugate_le φ hφ) y

/-- The actual lower truncation in CEK equation (61). -/
def lowerTruncate (φ : E → EReal) (M : ℝ) : E → EReal :=
  fun x => max (φ x) ((-M : ℝ) : EReal)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A single finite-value witness makes the lower truncation proper;
the input need not be convex, nonnegative, or globally finite. -/
theorem lowerTruncate_proper (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) : ProperPotential (lowerTruncate φ M) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact ne_of_gt ((EReal.bot_lt_coe (-M)).trans_le (le_max_right _ _))
  · obtain ⟨x, hx⟩ := hfinite
    refine ⟨x, ne_of_lt ?_⟩
    exact max_lt (Ne.lt_top hx) (EReal.coe_lt_top (-M))

/-- Both sides of the truncation/conjugation construction are proper,
so the triple-conjugate identity has hypotheses available from the data. -/
theorem legendre_lowerTruncate_proper (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) : ProperPotential (legendre (lowerTruncate φ M)) := by
  refine ⟨legendre_ne_bot _ (lowerTruncate_proper φ M hfinite), 0, ?_⟩
  exact ne_of_lt ((legendre_zero_le_of_lower_bound _ M
    (fun x => le_max_right _ _)).trans_lt (EReal.coe_lt_top M))

/-- Every affine summand of the actual extended-real conjugate is continuous,
including when its fixed intercept is an infinite value. -/
theorem continuous_legendre_summand (φ : E → EReal) (x : E) :
    Continuous (fun y : E => (inner ℝ x y : EReal) - φ x) := by
  by_cases hb : φ x = ⊥
  · simpa only [hb, EReal.coe_sub_bot] using
      (continuous_const : Continuous (fun _ : E => (⊤ : EReal)))
  by_cases ht : φ x = ⊤
  · simpa only [ht, EReal.sub_top] using
      (continuous_const : Continuous (fun _ : E => (⊥ : EReal)))
  lift φ x to ℝ using ⟨ht, hb⟩ with r hr
  have hc : Continuous (fun y : E => inner ℝ x y - r) :=
    (continuous_const.inner continuous_id).sub continuous_const
  simpa only [Function.comp_def, ← hr, ← EReal.coe_sub] using continuous_coe_real_ereal.comp hc

/-- The conjugate is lower semicontinuous for any extended-real input;
no properness, convexity, finite dimension or global finiteness is required. -/
theorem lowerSemicontinuous_legendre (φ : E → EReal) :
    LowerSemicontinuous (legendre φ) := by
  exact lowerSemicontinuous_iSup (fun x =>
    (continuous_legendre_summand φ x).lowerSemicontinuous)

/-- The real epigraph of the conjugate is convex for any extended-real input.
The special values in the intercept are handled before real convex combinations. -/
theorem convex_epigraph_legendre (φ : E → EReal) :
    Convex ℝ {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by
  intro p hp q hq a b ha hb hab
  change legendre φ (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  apply iSup_le
  intro x
  have hp' := (le_iSup (fun z : E => (inner ℝ z p.1 : EReal) - φ z) x).trans hp
  have hq' := (le_iSup (fun z : E => (inner ℝ z q.1 : EReal) - φ z) x).trans hq
  by_cases ht : φ x = ⊤
  · simp only [ht, EReal.sub_top, bot_le]
  by_cases hbot : φ x = ⊥
  · have hbad : (⊤ : EReal) ≤ (p.2 : EReal) := by
      simpa only [hbot, EReal.coe_sub_bot] using hp'
    exact False.elim ((not_le_of_gt (EReal.coe_lt_top p.2)) hbad)
  lift φ x to ℝ using ⟨ht, hbot⟩ with r hr
  have hpReal : inner ℝ x p.1 - r ≤ p.2 := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [← hr, ← EReal.coe_sub] using hp'
  have hqReal : inner ℝ x q.1 - r ≤ q.2 := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [← hr, ← EReal.coe_sub] using hq'
  have hweighted := add_le_add (mul_le_mul_of_nonneg_left hpReal ha)
    (mul_le_mul_of_nonneg_left hqReal hb)
  rw [← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  simp only [inner_add_right, inner_smul_right]
  have hprod : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith only [hprod, hweighted]

/-- Nonemptiness of the primal's effective domain is exactly what excludes
negative infinity in its conjugate. Input values `-∞` need not be ruled out. -/
theorem legendre_ne_bot_iff (φ : E → EReal) (y : E) :
    legendre φ y ≠ ⊥ ↔ ∃ x, φ x ≠ ⊤ := by
  constructor
  · intro h
    by_contra hnone
    have htop : ∀ x, φ x = ⊤ := by simpa only [not_exists, not_not] using hnone
    have hbottom : legendre φ y = ⊥ := by simp [legendre, htop]
    exact h hbottom
  · rintro ⟨x, hx⟩
    by_cases hb : φ x = ⊥
    · have htop : legendre φ y = ⊤ := by
        apply eq_top_iff.mpr
        change (⊤ : EReal) ≤ ⨆ z : E, (inner ℝ z y : EReal) - φ z
        simpa only [hb, EReal.coe_sub_bot] using
          (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
      simp only [htop, ne_eq, top_ne_bot, not_false_eq_true]
    · lift φ x to ℝ using ⟨hx, hb⟩ with r hr
      have hbound : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
        change ((inner ℝ x y - r : ℝ) : EReal) ≤
          ⨆ z : E, (inner ℝ z y : EReal) - φ z
        simpa only [← hr, EReal.coe_sub] using
          (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
      exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hbound)

/-- Conjugation produces a convex potential from precisely a nonempty effective
domain, without any convexity or lower-semicontinuity premise on the primal. -/
theorem convexPotential_legendre (φ : E → EReal) (hfinite : ∃ x, φ x ≠ ⊤) :
    ConvexPotential (legendre φ) :=
  ⟨fun y => (legendre_ne_bot_iff φ y).mpr hfinite, convex_epigraph_legendre φ⟩

namespace ConvexPotential

/-- The effective domain `{ψ ≠ ⊤}` of a convex potential is convex. -/
theorem convex_domain {ψ : E → EReal} (hψ : ConvexPotential ψ) : Convex ℝ {x | ψ x ≠ ⊤} := by
  have hset : {x | ψ x ≠ ⊤} =
      (LinearMap.fst ℝ E ℝ) '' {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} := by
    ext x
    constructor
    · intro hx
      refine ⟨(x, (ψ x).toReal), ?_, rfl⟩
      change ψ x ≤ ((ψ x).toReal : EReal)
      rw [EReal.coe_toReal hx (hψ.1 x)]
    · rintro ⟨p, hp, rfl⟩
      exact ne_top_of_le_ne_top (EReal.coe_ne_top p.2) hp
  rw [hset]
  exact hψ.2.linear_image _

/-- The real representative `(ψ ·).toReal` of a convex potential is convex on the effective
domain. -/
theorem convexOn_toReal {ψ : E → EReal} (hψ : ConvexPotential ψ) :
    ConvexOn ℝ {x | ψ x ≠ ⊤} (fun x => (ψ x).toReal) := by
  have hepi : {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} =
      {p : E × ℝ | p.1 ∈ {x | ψ x ≠ ⊤} ∧ (ψ p.1).toReal ≤ p.2} := by
    ext p
    constructor
    · intro hp
      change ψ p.1 ≤ (p.2 : EReal) at hp
      have ht : ψ p.1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top p.2) hp
      refine ⟨ht, ?_⟩
      rw [← EReal.coe_toReal ht (hψ.1 p.1)] at hp
      exact EReal.coe_le_coe_iff.mp hp
    · rintro ⟨ht, hp⟩
      change ψ p.1 ≤ (p.2 : EReal)
      rw [← EReal.coe_toReal ht (hψ.1 p.1)]
      exact EReal.coe_le_coe_iff.mpr hp
  have hc := hψ.2
  rw [hepi] at hc
  exact convexOn_of_convex_epigraph hc

end ConvexPotential

/-- The CEK lower bound persists through biconjugation. -/
theorem lower_bound_biconjugate (φ : E → EReal) (M : ℝ)
    (hlower : ∀ x, ((-M : ℝ) : EReal) ≤ φ x) (x : E) :
    ((-M : ℝ) : EReal) ≤ legendre (legendre φ) x := by
  have hzero := legendre_zero_le_of_lower_bound φ M hlower
  have hneg : ((-M : ℝ) : EReal) ≤ -legendre φ 0 := by
    simpa only [EReal.coe_neg] using (EReal.neg_le_neg_iff.mpr hzero)
  have hterm : -legendre φ 0 ≤ legendre (legendre φ) x := by
    change -legendre φ 0 ≤ ⨆ z : E, (inner ℝ z x : EReal) - legendre φ z
    simpa only [inner_zero_left, EReal.coe_zero, zero_sub] using
      (le_iSup (fun z : E => (inner ℝ z x : EReal) - legendre φ z) 0)
  exact hneg.trans hterm

/-- CEK Proposition 12's actual truncation/convexification has a convex lsc proper
output, retains the lower bound and pointwise upper bound, and preserves its
conjugate. Only a finite primal witness is needed; input convexity is unnecessary. -/
theorem lowerTruncate_convexification (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) :
    let g := lowerTruncate φ M
    let c := legendre (legendre g)
    ConvexPotential c ∧ LowerSemicontinuous c ∧ ProperPotential c ∧
      (∀ x, ((-M : ℝ) : EReal) ≤ c x ∧ c x ≤ g x) ∧
      (∀ y, legendre c y = legendre g y) := by
  dsimp only
  have hg := lowerTruncate_proper φ M hfinite
  have hdual := legendre_lowerTruncate_proper φ M hfinite
  have hc := convexPotential_legendre (legendre (lowerTruncate φ M)) hdual.2
  refine ⟨hc, lowerSemicontinuous_legendre _, ?_, ?_, triconjugate_eq _ hg hdual⟩
  · obtain ⟨x, hx⟩ := hg.2
    refine ⟨hc.1, x, ne_of_lt ?_⟩
    exact (biconjugate_le _ hg x).trans_lt (Ne.lt_top hx)
  · intro x
    exact ⟨lower_bound_biconjugate _ M (fun y => le_max_right _ _) x,
      biconjugate_le _ hg x⟩

section RadialClosure

open Filter Set
open scoped Topology

/-- The actual conjugate of the radially closed extension is the supremum of
its genuine affine terms on the original open interior. Boundary terms are
obtained by the actual radial limit; terms outside the closure are bottom. -/
theorem legendre_eq_interior_sup {K : Set E} (hK : IsOpen K) (hKconv : Convex ℝ K)
    (h0 : (0 : E) ∈ K) (ψ : E → EReal)
    (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
    (hoff : ∀ x ∉ closure K, ψ x = ⊤) (y : E) :
    legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x := by
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hx : x ∈ closure K
    · have hinside : ∀ᶠ t : ℝ in 𝓝[<] 1, t • x ∈ K := by
        have hpos : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t :=
          nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
        filter_upwards [hpos, self_mem_nhdsWithin] with t ht0 ht1
        have hi :=
          hKconv.combo_interior_closure_mem_interior (by rwa [hK.interior_eq]) hx
            (sub_pos.mpr ht1) ht0.le (by ring : (1 - t) + t = 1)
        simpa only [smul_zero, zero_add, hK.interior_eq] using hi
      have hi :
        Tendsto (fun t : ℝ => (inner ℝ (t • x) y : EReal)) (𝓝[<] 1) (𝓝 (inner ℝ x y : EReal)) := by
        have hc : Continuous (fun t : ℝ => (inner ℝ (t • x) y : EReal)) := by
          exact
            continuous_coe_real_ereal.comp
              ((continuous_id.smul continuous_const).inner continuous_const)
        simpa only [one_smul] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      have hn := (continuous_neg.tendsto (ψ x)).comp (hrad x)
      have ht :
        Tendsto (fun t : ℝ => (inner ℝ (t • x) y : EReal) - ψ (t • x)) (𝓝[<] 1)
          (𝓝 ((inner ℝ x y : EReal) - ψ x)) := by
        simpa only [sub_eq_add_neg, Function.comp_def] using
          (EReal.continuousAt_add (p := ((inner ℝ x y : EReal), -ψ x))
                (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))).tendsto.comp
            (hi.prodMk_nhds hn)
      apply le_of_tendsto ht
      filter_upwards [hinside] with t ht
      exact le_iSup_of_le (t • x) (le_iSup_of_le ht le_rfl)
    · simp only [hoff x hx, EReal.sub_top, bot_le]
  · apply iSup_le
    intro x
    apply iSup_le
    intro _
    exact le_iSup (fun z : E => (inner ℝ z y : EReal) - ψ z) x

end RadialClosure

end FunctionalInequalities.Analysis

/-! ### CEK Proposition 12: Legendre bounds and interior control -/

namespace FunctionalInequalities.Analysis


section
-- The Legendre transform of the norm.

open Set Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Exact norm conjugate: zero on the closed unit ball and infinity outside. -/
theorem legendre_norm (y : E) :
    legendre (fun x : E => (‖x‖ : EReal)) y = if ‖y‖ ≤ 1 then 0 else ⊤ := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [ite_eq_left hy]
    apply le_antisymm
    · apply iSup_le
      intro x
      rw [← EReal.coe_sub]
      apply EReal.coe_nonpos.mpr
      have h := (real_inner_le_norm x y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg x))
      simpa only [mul_one] using sub_nonpos.mpr h
    · simpa only [legendre, inner_zero_left, norm_zero, EReal.coe_zero, sub_zero] using
        (le_iSup (fun x : E => (inner ℝ x y : EReal) - (‖x‖ : EReal)) 0)
  · rw [ite_eq_right hy]
    by_contra ht
    have hb := (legendre_ne_bot_iff (fun x : E => (‖x‖ : EReal)) y).mpr ⟨0, by simp⟩
    lift legendre (fun x : E => (‖x‖ : EReal)) y to ℝ using ⟨ht, hb⟩ with r hr
    let d : ℝ := ‖y‖ ^ 2 - ‖y‖
    have hd : 0 < d := by dsimp [d]; nlinarith [lt_of_not_ge hy]
    let k : ℝ := (|r| + 1) / d
    have hk : 0 < k := div_pos (by positivity) hd
    have hterm : inner ℝ (k • y) y - ‖k • y‖ = |r| + 1 := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
        abs_of_pos hk]
      calc
        k * ‖y‖ ^ 2 - k * ‖y‖ = k * d := by dsimp [d]; ring
        _ = _ := div_mul_cancel₀ _ hd.ne'
    have h := le_iSup (fun x : E => (inner ℝ x y : EReal) - (‖x‖ : EReal)) (k • y)
    change
      (inner ℝ (k • y) y : EReal) - (‖k • y‖ : EReal) ≤
        legendre (fun x : E => (‖x‖ : EReal)) y at h
    rw [← EReal.coe_sub, hterm, ← hr] at h
    have hreal := EReal.coe_le_coe_iff.mp h
    linarith [le_abs_self r]

end

end FunctionalInequalities.Analysis
