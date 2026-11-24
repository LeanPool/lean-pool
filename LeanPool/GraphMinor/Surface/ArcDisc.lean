/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ArcPlane
public import LeanPool.GraphMinor.Surface.DiscMerge
public import LeanPool.GraphMinor.Surface.DiscsInSurface
public import LeanPool.GraphMinor.Surface.Cap
import Mathlib.Analysis.Complex.ReImTopology

/-!
# A closed disc around an arc

Every arc `L` of a closed surface lies inside a closed disc (`exists_disc_of_arc`), and this disc
can be chosen with a chart that makes `L` a straight segment.

Near an arc in a chart we use the strip coordinates of `exists_straight`: the arc lies on the real
axis (`exists_stripChart`). A map of the plane that is the identity on the frontier of a compact set
extends to the surface by the identity (`exists_glue`).

To swallow an arc, suppose that a disc holds the first part of it. The next part lies in a chart.
Slide the points of this strip to the left along the real axis, by a homeomorphism `h` of the
surface that is the identity off a thin rectangle. If the rectangle is thin enough, `h` maps all of
the longer arc into the disc, so the preimage under `h` of the disc holds the longer arc.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter Complex

local notation "𝕀" => unitInterval

variable {T : Type} [TopologicalSpace T]

/-- `K` is an injective continuous open map on the open set `O` of the plane. -/
structure StripChart (O : Set ℂ) (K : ℂ → T) : Prop where
  isOpen : IsOpen O
  hc : ContinuousOn K O
  hi : InjOn K O
  ho : ∀ W, IsOpen W → W ⊆ O → IsOpen (K '' W)

theorem exp_strip_inj {x x' y y' : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx' : x' ∈ Ioo
  (-Real.pi) Real.pi)
    (hy : 0 < 1 + y) (hy' : 0 < 1 + y')
    (h : ((1 + y : ℝ) : ℂ) * exp (x * I) = ((1 + y' : ℝ) : ℂ) * exp (x' * I)) : x = x' ∧ y = y'
      := by
  have h1 := congrArg norm h
  rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I, Complex.norm_real,
    Complex.norm_real,
    Real.norm_of_nonneg hy.le, Real.norm_of_nonneg hy'.le, mul_one, mul_one] at h1
  have hyy : y = y' := by linarith
  subst hyy
  have h2 : exp (x * I) = exp (x' * I) := mul_left_cancel₀ (by exact_mod_cast hy.ne') h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h2
  have h3 : x = x' + n * (2 * Real.pi) := by
    have h4 := congrArg Complex.im hn
    simp at h4
    linarith
  have hpi := Real.pi_pos
  have h5 : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith [hx.2, hx'.1]
  have h6 : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by linarith [hx.1, hx'.2]
  have h7 : (n : ℝ) < 1 := by nlinarith
  have h8 : (-1 : ℝ) < n := by nlinarith
  have h9 : n = 0 := by
    have h10 : n < 1 := by exact_mod_cast h7
    have h11 : -1 < n := by exact_mod_cast h8
    omega
  subst h9
  exact ⟨by simpa using h3, rfl⟩

/-- An arc in a chart of a surface lies on the real axis of a strip chart. -/
theorem exists_stripChart (hman : ∀ x : T, IsManifoldPoint x) {R : ℝ} {U : Set T} {h : T
  → ℂ} {g : ℂ → T}
    (c : BallChart R U h g) {a : 𝕀 → T} (ha : IsArcMap a) (hU : range a ⊆ U) :
    ∃ (O : Set ℂ) (K : ℂ → T) (θ : 𝕀 → ℝ), StripChart O K ∧ Continuous θ ∧ StrictMono θ ∧
      ∀ t, (θ t : ℂ) ∈ O ∧ K (θ t) = a t := by
  have hac : Continuous fun t => h (a t) :=
    c.hc.comp_continuous ha.1 fun t => hU (mem_range_self t)
  have hai : Function.Injective fun t => h (a t) := fun s t he => ha.2 (by
    have := congrArg g he
    rwa [c.gh (hU (mem_range_self s)), c.gh (hU (mem_range_self t))] at this)
  obtain ⟨G, θ, hθc, hθm, hθr, hGa⟩ := exists_straight (a := fun t => h (a t)) ⟨hac, hai⟩
  let S : ℂ → ℂ := fun z => G.symm (((1 + z.im : ℝ) : ℂ) * exp ((z.re : ℂ) * I))
  have hSc : Continuous S := by
    refine G.symm.continuous.comp ?_
    have h1 : Continuous fun z : ℂ => (z.re : ℂ) := continuous_ofReal.comp continuous_re
    have h2 : Continuous fun z : ℂ => ((1 + z.im : ℝ) : ℂ) := continuous_ofReal.comp (by fun_prop)
    fun_prop
  let O : Set ℂ := {z | z.re ∈ Ioo (-Real.pi) Real.pi ∧ z.im ∈ Ioo (-1 : ℝ) 1 ∧ S z ∈ ball 0 R}
  have hOo : IsOpen O := by
    refine IsOpen.inter (isOpen_Ioo.preimage continuous_re) (IsOpen.inter
      (isOpen_Ioo.preimage continuous_im) (isOpen_ball.preimage hSc))
  have hK : ContinuousOn (fun z => g (S z)) O :=
    c.gc.comp hSc.continuousOn fun z hz => hz.2.2
  have hKi : InjOn (fun z => g (S z)) O := by
    intro z hz w hw he
    have h1 : S z = S w := by
      have := congrArg h he
      simpa only [c.hg hz.2.2, c.hg hw.2.2] using this
    have h2 := exp_strip_inj hz.1 hw.1 (by linarith [hz.2.1.1]) (by linarith [hw.2.1.1])
      (G.symm.injective h1)
    exact Complex.ext h2.1 h2.2
  refine ⟨O, fun z => g (S z), θ, ⟨hOo, hK, hKi, fun W hW hWO => ?_⟩, hθc, hθm, fun t => ?_⟩
  · exact isOpen_image_of_manifold hW (hK.mono hWO) (hKi.mono hWO) fun z _ => hman _
  · have hS : S (θ t) = h (a t) := by
      simp only [S, ofReal_re, ofReal_im, add_zero, ofReal_one, one_mul]
      rw [← hGa, G.symm_apply_apply]
    refine ⟨⟨by simpa using hθr t, by simp, ?_⟩, ?_⟩
    · rw [hS]
      exact c.hm (hU (mem_range_self t))
    · simp only [hS]
      exact c.gh (hU (mem_range_self t))

/-- A map of the plane that is the identity on the frontier of a compact set `R` extends, by the
identity, to the surface. There is a space of parameters, so that this gives homotopies as well. -/
theorem exists_glue [T2Space T] {P : Type*} [TopologicalSpace P] {O : Set ℂ} {K : ℂ → T}
  (hK : StripChart O K)
    {R : Set ℂ} (hR : IsCompact R) (hRO : R ⊆ O) (Φ : P × ℂ → ℂ) (hΦ : ContinuousOn Φ (univ ×ˢ R))
    (hm : ∀ p, ∀ z ∈ R, Φ (p, z) ∈ R) (hid : ∀ p, ∀ z ∈ frontier R, Φ (p, z) = z) :
    ∃ c : P × T → T, Continuous c ∧ (∀ p, ∀ z ∈ R, c (p, K z) = K (Φ (p, z)))
      ∧ ∀ p, ∀ x ∉ K '' R, c (p, x) = x := by
  classical
  rcases isEmpty_or_nonempty ℂ with he | he
  · exact (he.false 0).elim
  let J : T → ℂ := Function.invFunOn K O
  have hJ : ∀ z ∈ O, J (K z) = z := fun z hz => hK.hi.leftInvOn_invFunOn hz
  have hKR : IsClosed (K '' R) := (hR.image_of_continuousOn (hK.hc.mono hRO)).isClosed
  have hJc : ContinuousOn J (K '' R) := by
    rw [continuousOn_iff_isClosed]
    intro t ht
    refine ⟨K '' (R ∩ t), ((hR.inter_right ht).image_of_continuousOn (hK.hc.mono
      (inter_subset_left.trans hRO))).isClosed, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, z, hz, rfl⟩
      have h1 : z ∈ t := by simpa [hJ z (hRO hz)] using hx
      exact ⟨⟨z, ⟨hz, h1⟩, rfl⟩, ⟨z, hz, rfl⟩⟩
    · rintro ⟨⟨z, hz, rfl⟩, hx⟩
      refine ⟨?_, hx⟩
      change J (K z) ∈ t
      rw [hJ z (hRO hz.1)]
      exact hz.2
  have hint : IsOpen (K '' interior R) := hK.ho _ isOpen_interior (interior_subset.trans hRO)
  let c : P × T → T := fun q => if q.2 ∈ K '' R then K (Φ (q.1, J q.2)) else q.2
  have hc1 : ContinuousOn c (univ ×ˢ (K '' R)) := by
    have h1 : ContinuousOn (fun q : P × T => K (Φ (q.1, J q.2))) (univ ×ˢ (K '' R)) := by
      have h2 : ContinuousOn (fun q : P × T => (q.1, J q.2)) (univ ×ˢ (K '' R)) :=
        continuousOn_fst.prodMk (hJc.comp continuousOn_snd fun q hq => hq.2)
      have h3 : MapsTo (fun q : P × T => (q.1, J q.2)) (univ ×ˢ (K '' R)) (univ ×ˢ R) := by
        rintro ⟨p, x⟩ ⟨-, z, hz, rfl⟩
        refine ⟨mem_univ _, ?_⟩
        change J (K z) ∈ R
        rwa [hJ z (hRO hz)]
      have h4 := hΦ.comp h2 h3
      refine (hK.hc.comp h4 ?_)
      rintro ⟨p, x⟩ ⟨-, z, hz, rfl⟩
      have h5 : J (K z) = z := hJ z (hRO hz)
      change Φ (p, J (K z)) ∈ O
      rw [h5]
      exact hRO (hm p z hz)
    refine h1.congr ?_
    rintro ⟨p, x⟩ ⟨-, hx⟩
    exact ite_eq_left hx
  have hc2 : ContinuousOn c (univ ×ˢ (K '' interior R)ᶜ) := by
    have h1 : ContinuousOn (fun q : P × T => q.2) (univ ×ˢ (K '' interior R)ᶜ) := continuousOn_snd
    refine h1.congr ?_
    rintro ⟨p, x⟩ ⟨-, hx⟩
    change (if x ∈ K '' R then _ else _) = _
    split_ifs with hxR
    · obtain ⟨z, hz, rfl⟩ := hxR
      have hfr : z ∈ frontier R := by
        rw [hR.isClosed.frontier_eq]
        exact ⟨hz, fun hi => hx ⟨z, hi, rfl⟩⟩
      change K (Φ (p, J (K z))) = K z
      rw [hJ z (hRO hz), hid p z hfr]
    · rfl
  have hcov : (univ ×ˢ (K '' R)) ∪ (univ ×ˢ (K '' interior R)ᶜ) = (univ : Set (P × T)) := by
    ext ⟨p, x⟩
    simp only [mem_union, mem_prod, mem_univ, true_and, iff_true]
    by_cases hx : x ∈ K '' interior R
    · exact .inl (image_mono interior_subset hx)
    · exact .inr hx
  refine ⟨c, ?_, fun p z hz => ?_, fun p x hx => ?_⟩
  · rw [← continuousOn_univ, ← hcov]
    exact hc1.union_of_isClosed hc2 (isClosed_univ.prod hKR) (isClosed_univ.prod
      hint.isClosed_compl)
  · change (if K z ∈ K '' R then _ else _) = _
    rw [ite_eq_left (show K z ∈ K '' R from ⟨z, hz, rfl⟩), hJ z (hRO hz)]
  · exact ite_eq_right hx

/-- A convex broken line: it fixes the two ends `a`, `b`, and sends `m` to the smaller number `x`.
-/
theorem exists_slide_fun {a x m b : ℝ} (h1 : a < x) (h2 : x < m) (h3 : m < b) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ StrictMono ψ ∧ ψ a = a ∧ ψ b = b ∧ ψ m = x ∧ ∀ y ≤ b, a ≤ y → ψ y
      ≤ y := by
  set l := (x - a) / (m - a) with hl
  set μ := (b - x) / (b - m) with hμ
  have hma : 0 < m - a := by linarith
  have hbm : 0 < b - m := by linarith
  have hl0 : 0 < l := div_pos (by linarith) hma
  have hl1 : l < 1 := (div_lt_one hma).mpr (by linarith)
  have hμ1 : 1 < μ := (one_lt_div hbm).mpr (by linarith)
  have e1 : l * (m - a) = x - a := div_mul_cancel₀ _ hma.ne'
  have e2 : μ * (b - m) = b - x := div_mul_cancel₀ _ hbm.ne'
  refine ⟨fun y => max (a + l * (y - a)) (b + μ * (y - b)), by fun_prop, ?_, ?_, ?_, ?_, ?_⟩
  · intro y z hyz
    apply max_lt
    · exact lt_max_of_lt_left (by nlinarith)
    · exact lt_max_of_lt_right (by nlinarith)
  · simp only
    rw [max_eq_left (by nlinarith)]
    ring
  · simp only
    rw [max_eq_right (by nlinarith)]
    ring
  · simp only
    rw [max_eq_left (by nlinarith)]
    linarith
  · intro y hy hay
    simp only
    exact max_le (by nlinarith) (by nlinarith)

/-- A slide in a rectangle of a strip chart: a homeomorphism of the surface that is the identity off
the rectangle `R` and moves points of `R` to the left, and by the function `ψ` on the real axis. -/
theorem exists_slide [CompactSpace T] [T2Space T] {O : Set ℂ} {K : ℂ → T}
  (hK : StripChart O K) {a b ε : ℝ} (hab : a < b)
    (hε : 0 < ε) (hRO : Icc a b ×ℂ Icc (-ε) ε ⊆ O) {ψ : ℝ → ℝ} (hc : Continuous ψ)
      (hm : StrictMono ψ) (ha : ψ a = a)
    (hb : ψ b = b) (hle : ∀ y ≤ b, a ≤ y → ψ y ≤ y) :
    ∃ e : T ≃ₜ T, (∀ x ∉ K '' (Icc a b ×ℂ Icc (-ε) ε), e x = x) ∧ (∀ x ∈ Icc a b, e (K x) = K
      (ψ x)) ∧
      ∀ z ∈ Icc a b ×ℂ Icc (-ε) ε, ∃ w ∈ Icc a b ×ℂ Icc (-ε) ε, w.re ≤ z.re ∧ w.im = z.im ∧ e (K z)
        = K w := by
  classical
  set R := Icc a b ×ℂ Icc (-ε) ε with hR
  have hRc : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  let s : ℂ → ℝ := fun z => 1 - |z.im| / ε
  have hs : ∀ z ∈ R, s z ∈ Icc (0 : ℝ) 1 := fun z hz => by
    have h1 : |z.im| ≤ ε := abs_le.mpr hz.2
    refine ⟨?_, by simp only [s]; linarith [div_nonneg (abs_nonneg z.im) hε.le]⟩
    simp only [s]
    linarith [(div_le_one hε).mpr h1]
  let f : ℝ → ℝ → ℝ := fun t x => x + t * (ψ x - x)
  have hfm : ∀ t ∈ Icc (0 : ℝ) 1, StrictMono (f t) := fun t ht x y h => by
    have h1 := hm h
    simp only [f]
    have h2 : 0 ≤ (1 - t) * (y - x) := mul_nonneg (by linarith [ht.2]) (by linarith)
    have h3 : 0 ≤ t * (ψ y - ψ x) := mul_nonneg ht.1 (by linarith)
    rcases lt_or_eq_of_le ht.2 with h4 | h4
    · have h5 : 0 < (1 - t) * (y - x) := mul_pos (by linarith) (by linarith)
      nlinarith
    · subst h4
      linarith
  have hfa : ∀ t, f t a = a := fun t => by simp [f, ha]
  have hfb : ∀ t, f t b = b := fun t => by simp [f, hb]
  have hfc : ∀ t, Continuous (f t) := fun t => by simp only [f]; fun_prop
  have hfl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc a b, f t x ≤ x := fun t ht x hx => by
    have := hle x hx.2 hx.1
    simp only [f]
    nlinarith [ht.1, mul_nonneg ht.1 (sub_nonneg.mpr this)]
  have hfI : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc a b, f t x ∈ Icc a b := fun t ht x hx =>
    ⟨by rw [← hfa t]; exact (hfm t ht).monotone hx.1, (hfl t ht x hx).trans hx.2⟩
  let Φ : Unit × ℂ → ℂ := fun q => (f (s q.2) q.2.re : ℂ) + q.2.im * I
  have hΦc : Continuous Φ := by
    simp only [Φ, f, s]
    have : Continuous fun q : Unit × ℂ => q.2.re := continuous_re.comp continuous_snd
    have h2 : Continuous fun q : Unit × ℂ => q.2.im := continuous_im.comp continuous_snd
    have h3 : Continuous fun q : Unit × ℂ => ψ q.2.re := hc.comp this
    have h4 : Continuous fun q : Unit × ℂ => (q.2.re + (1 - |q.2.im| / ε) *
      (ψ q.2.re - q.2.re) : ℝ) := by fun_prop
    exact (continuous_ofReal.comp h4).add ((continuous_ofReal.comp h2).mul continuous_const)
  have hΦre : ∀ q, (Φ q).re = f (s q.2) q.2.re := fun q => by simp [Φ]
  have hΦim : ∀ q, (Φ q).im = q.2.im := fun q => by simp [Φ]
  have hΦR : ∀ z ∈ R, Φ ((), z) ∈ R := fun z hz => by
    refine mem_reProdIm.mpr ⟨?_, ?_⟩
    · rw [hΦre]
      exact hfI _ (hs z hz) _ hz.1
    · rw [hΦim]
      exact hz.2
  have hfr : ∀ z ∈ frontier R, Φ ((), z) = z := by
    intro z hz
    rw [hRc.isClosed.frontier_eq, hR, interior_reProdIm, interior_Icc, interior_Icc] at hz
    obtain ⟨hz1, hz2⟩ := hz
    apply Complex.ext
    · rw [hΦre]
      simp only [f]
      by_cases h1 : z.re = a
      · rw [h1, ha]; ring
      by_cases h2 : z.re = b
      · rw [h2, hb]; ring
      have h3 : z.im ∉ Ioo (-ε) ε := fun h3 => hz2 ⟨⟨lt_of_le_of_ne hz1.1.1
        (Ne.symm h1), lt_of_le_of_ne hz1.1.2 h2⟩, h3⟩
      have h4 : |z.im| = ε := by
        have h5 := abs_le.mpr hz1.2
        refine le_antisymm h5 ?_
        by_contra h6
        exact h3 (abs_lt.mp (not_le.mp h6))
      have h5 : s z = 0 := by simp only [s]; rw [h4, div_self hε.ne']; ring
      rw [h5]
      ring
    · rw [hΦim]
  obtain ⟨c, hcc, hc1, hc2⟩ := exists_glue hK hRc hRO Φ hΦc.continuousOn (fun _ z hz => hΦR z hz)
    (fun _ z hz => hfr z hz)
  let h : T → T := fun x => c ((), x)
  have hhc : Continuous h := hcc.comp (by fun_prop)
  have hinj : Function.Injective h := by
    have key : ∀ z ∈ R, ∀ w ∈ R, Φ ((), z) = Φ ((), w) → z = w := by
      intro z hz w hw he
      have h1 : z.im = w.im := by
        have := congrArg Complex.im he
        rwa [hΦim, hΦim] at this
      have h2 : s z = s w := by simp only [s, h1]
      have h3 := congrArg Complex.re he
      rw [hΦre, hΦre] at h3
      simp only at h3
      rw [h2] at h3
      exact Complex.ext ((hfm _ (hs w hw)).injective h3) h1
    intro x y he
    by_cases hx : x ∈ K '' R <;> by_cases hy : y ∈ K '' R
    · obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      simp only [h, hc1 _ z hz, hc1 _ w hw] at he
      rw [key z hz w hw (hK.hi (hRO (hΦR z hz)) (hRO (hΦR w hw)) he)]
    · obtain ⟨z, hz, rfl⟩ := hx
      simp only [h, hc1 _ z hz, hc2 _ y hy] at he
      exact absurd ⟨_, hΦR z hz, he⟩ hy
    · obtain ⟨w, hw, rfl⟩ := hy
      simp only [h, hc1 _ w hw, hc2 _ x hx] at he
      exact absurd ⟨_, hΦR w hw, he.symm⟩ hx
    · simpa only [h, hc2 _ x hx, hc2 _ y hy] using he
  have hsurj : Function.Surjective h := by
    intro y
    by_cases hy : y ∈ K '' R
    · obtain ⟨w, hw, rfl⟩ := hy
      have hsw := hs w hw
      obtain ⟨x, hx, hxe⟩ : w.re ∈ f (s w) '' Icc a b := by
        refine intermediate_value_Icc hab.le (hfc _).continuousOn ?_
        rw [hfa, hfb]
        exact hw.1
      refine ⟨K ((x : ℂ) + w.im * I), ?_⟩
      have hz : ((x : ℂ) + w.im * I) ∈ R := ⟨by simpa using hx, by simpa using hw.2⟩
      simp only [h]
      rw [hc1 _ _ hz]
      congr 1
      apply Complex.ext
      · rw [hΦre]
        have h1 : s ((x : ℂ) + w.im * I) = s w := by simp [s]
        rw [h1]
        simpa using hxe
      · rw [hΦim]
        simp
    · exact ⟨y, hc2 _ y hy⟩
  let e : T ≃ₜ T := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective h ⟨hinj, hsurj⟩) hhc
  have he : ∀ x, e x = c ((), x) := fun _ => rfl
  refine ⟨e, fun x hx => by rw [he, hc2 _ x hx], fun x hx => ?_, fun z hz => ?_⟩
  · have hz : (x : ℂ) ∈ R := ⟨by simpa using hx, by simp [hε.le]⟩
    rw [he, hc1 _ _ hz]
    congr 1
    apply Complex.ext
    · rw [hΦre]
      have h1 : s (x : ℂ) = 1 := by simp [s]
      rw [h1]
      simp [f]
    · rw [hΦim]
      simp
  · refine ⟨Φ ((), z), hΦR z hz, ?_, hΦim _, by rw [he, hc1 _ z hz]⟩
    rw [hΦre]
    exact hfl _ (hs z hz) _ hz.1

theorem isOpen_discInt (hman : ∀ x : T, IsManifoldPoint x) {D : Set T}
  (hD : IsClosedDisc D) : IsOpen (discInt D) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  rw [c.discInt_eq]
  exact c.isOpen_image_ball hman

/-- A closed disc around a point of a closed surface, with the point inside. -/
theorem exists_disc_at (hT : IsClosedSurface T) (y : T) : ∃ D, IsClosedDisc D ∧ y ∈ discInt D := by
  obtain ⟨U, h, g, c, -, hy⟩ := (hT.2.2 y).exists_ballChart isOpen_univ (mem_univ _) (R := 2)
    (by norm_num)
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  have hD : IsClosedDisc (closedBall (0 : ℂ) 1) := (isClosedDisc_of_convex (convex_closedBall 0 1)
    (by
    rw [interior_closedBall _ one_ne_zero]
    exact ⟨0, by simp⟩) isBounded_closedBall isClosed_closedBall).1
  obtain ⟨h1, h2⟩ := c.image_disc hD hsub
  have hb : discBd (closedBall (0 : ℂ) 1) = sphere 0 1 := by
    rw [(isClosedDisc_of_convex (convex_closedBall 0 1) (by
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0, by simp⟩) isBounded_closedBall isClosed_closedBall).2,
        frontier_closedBall _ one_ne_zero]
  refine ⟨_, h1, ⟨0, by simp, hy⟩, ?_⟩
  rw [h2, hb]
  rintro ⟨z, hz, he⟩
  have h3 : z = 0 := by
    have h4 := congrArg h (he.trans hy.symm)
    rw [c.hg (hsub (sphere_subset_closedBall hz)), c.hg (show (0 : ℂ) ∈ ball 0 2 by simp)] at h4
    exact h4
  rw [h3] at hz
  simp at hz

theorem image_sub_compact {θ : 𝕀 → ℝ} (hθ : Continuous θ) {s t : 𝕀} (hst : s ≤ t) {x : ℝ}
  (hx : x ∈ Icc (θ s) (θ t)) :
    ∃ r ∈ Icc s t, θ r = x :=
  intermediate_value_Icc hst hθ.continuousOn hx

/-- One step of swallowing an arc. -/
theorem disc_step (hT : IsClosedSurface T) {a : 𝕀 → T} (ha : IsArcMap a) {τ₁ : 𝕀} (hτ : 0 < τ₁)
    (hB : ∀ τ < τ₁, ∃ D, IsClosedDisc D ∧ a '' Iic τ ⊆ discInt D) :
    ∃ D, IsClosedDisc D ∧ a '' Iic τ₁ ⊆ discInt D := by
  classical
  have hcpt : CompactSpace T := hT.1
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  obtain ⟨U, h, g, c, -, hy⟩ := (hT.2.2 (a τ₁)).exists_ballChart isOpen_univ (mem_univ _) (R
    := 1) one_pos
  have hUo : a ⁻¹' U ∈ 𝓝 τ₁ := by
    refine ha.1.continuousAt.preimage_mem_nhds (c.isOpen.mem_nhds ?_)
    rw [← hy]
    exact c.gm (by simp)
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hUo ⟨0, hτ⟩
  obtain ⟨τb, hb1, hb2⟩ := exists_between hl
  obtain ⟨D, hD, hDs⟩ := hB τb hb2
  have hDo := isOpen_discInt hman hD
  -- the arc in the chart
  have hne : τb ≠ τ₁ := hb2.ne
  let J : 𝕀 → T := subArc a τb τ₁
  have hJ : IsArcMap J := ha.sub hne
  have hJr : range J = a '' Icc τb τ₁ := range_subArc a hb2.le
  have hJU : range J ⊆ U := by
    rw [hJr]
    rintro _ ⟨t, ht, rfl⟩
    exact hsub ⟨hb1.trans_le ht.1, ht.2⟩
  obtain ⟨O, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart hman c hJ hJU
  set α := θ 0 with hα
  set β := θ 1 with hβ
  have hαβ : α < β := hθm zero_lt_one
  have hJ0 : J 0 = a τb := by simp [J, subArc_zero]
  have hbI : a τb ∈ discInt D := hDs ⟨τb, self_mem_Iic, rfl⟩
  have hV : J ⁻¹' discInt D ∈ 𝓝 (0 : 𝕀) := hJ.1.continuousAt.preimage_mem_nhds (hDo.mem_nhds
    (by rw [hJ0]; exact hbI))
  obtain ⟨u, hu, hus⟩ := exists_Ico_subset_of_mem_nhds hV ⟨1, zero_lt_one⟩
  obtain ⟨r₀, hr0, hr1⟩ := exists_between hu
  have hr01 : r₀ < 1 := hr1.trans_le u.2.2
  set x := θ r₀ with hx
  have hαx : α < x := hθm hr0
  have hxβ : x < β := hθm hr01
  -- the two open sets of the plane
  set A := a '' Iic τb with hA
  have hAc : IsClosed A := (isClosed_Iic.isCompact.image ha.1).isClosed
  let W₁ : Set ℂ := O ∩ K ⁻¹' discInt D
  let W₂ : Set ℂ := O ∩ K ⁻¹' Aᶜ
  have hW₁ : IsOpen W₁ := hK.hc.isOpen_inter_preimage hK.isOpen hDo
  have hW₂ : IsOpen W₂ := hK.hc.isOpen_inter_preimage hK.isOpen hAc.isOpen_compl
  have hS₁ : ((↑) : ℝ → ℂ) '' Icc α x ⊆ W₁ := by
    rintro _ ⟨y, hy', rfl⟩
    obtain ⟨r, hr, rfl⟩ := image_sub_compact hθc hr0.le hy'
    refine ⟨(hθ r).1, ?_⟩
    change K (θ r) ∈ discInt D
    rw [(hθ r).2]
    exact hus ⟨hr.1, hr.2.trans_lt hr1⟩
  have hS₂ : ((↑) : ℝ → ℂ) '' Icc x β ⊆ W₂ := by
    rintro _ ⟨y, hy', rfl⟩
    obtain ⟨r, hr, rfl⟩ := image_sub_compact hθc hr01.le hy'
    refine ⟨(hθ r).1, ?_⟩
    change K (θ r) ∉ A
    rw [(hθ r).2]
    rintro ⟨t, ht, he⟩
    have h1 : t = lerpI τb τ₁ r := ha.2 he
    have hrpos : (0 : ℝ) < r.1 := hr0.trans_le hr.1
    have hb3 : τb.1 < τ₁.1 := hb2
    have h2 : t.1 ≤ τb.1 := ht
    rw [h1] at h2
    change (1 - r.1) * τb.1 + r.1 * τ₁.1 ≤ τb.1 at h2
    nlinarith [mul_pos hrpos (sub_pos.mpr hb3)]
  obtain ⟨η₁, hη₁, ht₁⟩ := ((isCompact_Icc.image continuous_ofReal).exists_cthickening_subset_open
    hW₁ hS₁)
  obtain ⟨η₂, hη₂, ht₂⟩ := ((isCompact_Icc.image continuous_ofReal).exists_cthickening_subset_open
    hW₂ hS₂)
  set η := min η₁ η₂ with hη
  have hηpos : 0 < η := lt_min hη₁ hη₂
  set δ := min (η / 2) (1 : ℝ) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) one_pos
  have hδη : δ ≤ η / 2 := min_le_left _ _
  set R := Icc (α - δ) (β + δ) ×ℂ Icc (-δ) δ with hR
  -- points of the rectangle are near a point of the axis
  have near : ∀ z ∈ R, ∀ p q : ℝ, p ≤ q → z.re ∈ Icc (p - δ) (q + δ) → ∃ y ∈ Icc p q, ‖z - (y : ℂ)‖
    ≤ η := by
    intro z hz p q hpq hzr
    refine ⟨max p (min q z.re), ⟨le_max_left _ _, max_le hpq (min_le_left _ _)⟩, ?_⟩
    set y := max p (min q z.re) with hy'
    have h1 : |z.re - y| ≤ δ := by
      rw [abs_le]
      constructor
      · have : y ≤ max p z.re := max_le_max_left _ (min_le_right _ _)
        rcases le_total p z.re with h | h
        · rw [max_eq_right h] at this
          linarith [this, hδpos]
        · rw [max_eq_left h] at this
          linarith [hzr.1]
      · have h2 : min q z.re ≤ y := le_max_right _ _
        rcases le_total q z.re with h | h
        · rw [min_eq_left h] at h2
          linarith [hzr.2]
        · rw [min_eq_right h] at h2
          linarith
    have h2 : |z.im| ≤ δ := abs_le.mpr hz.2
    have h3 : ‖z - (y : ℂ)‖ ≤ |(z - (y : ℂ)).re| + |(z - (y : ℂ)).im| := norm_le_abs_re_add_abs_im _
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h3
    linarith
  have inW₁ : ∀ z ∈ R, z.re ≤ x → z ∈ W₁ := fun z hz hzx => by
    obtain ⟨y, hy', hn⟩ := near z hz α x hαx.le ⟨hz.1.1, by linarith⟩
    refine ht₁ (mem_cthickening_of_dist_le z (y : ℂ) _ _ ⟨y, hy', rfl⟩ ?_)
    rw [dist_eq_norm]
    exact hn.trans (min_le_left _ _)
  have inW₂ : ∀ z ∈ R, x ≤ z.re → z ∈ W₂ := fun z hz hzx => by
    obtain ⟨y, hy', hn⟩ := near z hz x β hxβ.le ⟨by linarith, hz.1.2⟩
    refine ht₂ (mem_cthickening_of_dist_le z (y : ℂ) _ _ ⟨y, hy', rfl⟩ ?_)
    rw [dist_eq_norm]
    exact hn.trans (min_le_right _ _)
  have hRO : R ⊆ O := fun z hz => by
    rcases le_total z.re x with h1 | h1
    · exact (inW₁ z hz h1).1
    · exact (inW₂ z hz h1).1
  obtain ⟨ψ, hψc, hψm, hψa, hψb, hψβ, hψl⟩ := exists_slide_fun (a := α - δ) (x := x) (m := β) (b
    := β + δ) (by linarith) hxβ (by linarith)
  obtain ⟨e, he1, he2, he3⟩ := exists_slide hK (a := α - δ) (b := β + δ) (ε := δ)
    (by linarith) hδpos hRO hψc hψm hψa hψb hψl
  have hDe := (hD.image (f := e.symm) (f' := e) e.symm.continuous.continuousOn
    e.continuous.continuousOn fun y _ => e.apply_symm_apply y)
  refine ⟨e.symm '' D, hDe.1, ?_⟩
  have key : ∀ t ≤ τ₁, e (a t) ∈ discInt D := by
    intro t ht
    rcases le_or_gt t τb with h1 | h1
    · have hmem : a t ∈ A := ⟨t, h1, rfl⟩
      by_cases hin : a t ∈ K '' R
      · obtain ⟨z, hz, hze⟩ := hin
        obtain ⟨w, hw, hwz, -, hew⟩ := he3 z hz
        have hzx : z.re ≤ x := by
          by_contra hc
          have := (inW₂ z hz (not_le.mp hc).le).2
          exact this (hze ▸ hmem)
        rw [← hze, hew]
        exact (inW₁ w hw (hwz.trans hzx)).2
      · rw [he1 _ hin]
        exact hDs hmem
    · obtain ⟨r, hr⟩ : ∃ r, lerpI τb τ₁ r = t := by
        have : t ∈ range (lerpI τb τ₁) := by
          rw [range_lerpI hb2.le]
          exact ⟨h1.le, ht⟩
        exact this
      have hJr' : a t = K (θ r) := by rw [(hθ r).2, ← hr]; rfl
      have hIcc : θ r ∈ Icc (α - δ) (β + δ) := ⟨by
        have : α ≤ θ r := hθm.monotone r.2.1
        linarith, by
        have : θ r ≤ β := hθm.monotone r.2.2
        linarith⟩
      rw [hJr', he2 _ hIcc]
      have hψlower : α - δ ≤ ψ (θ r) := by
        rw [← hψa]
        exact hψm.monotone hIcc.1
      have hψmem : ψ (θ r) ∈ Icc (α - δ) (β + δ) :=
        ⟨hψlower, (hψl _ hIcc.2 hIcc.1).trans hIcc.2⟩
      have hψR : ((ψ (θ r) : ℝ) : ℂ) ∈ R :=
        mem_reProdIm.mpr ⟨by simpa using hψmem, by simp [hδpos.le]⟩
      refine (inW₁ _ hψR ?_).2
      have h2 : θ r ≤ β := hθm.monotone r.2.2
      have h3 := hψm.monotone h2
      rw [hψβ] at h3
      simpa using h3
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨⟨e (a t), (key t ht).1, e.symm_apply_apply _⟩, ?_⟩
  rw [hDe.2]
  rintro ⟨w, hw, he⟩
  have : w = e (a t) := by rw [← he, e.apply_symm_apply]
  exact (key t ht).2 (this ▸ hw)

/-- **A closed disc around an arc.** In a closed surface, every arc lies inside a closed disc. -/
theorem exists_disc_of_arc (hT : IsClosedSurface T) {a : 𝕀 → T} (ha : IsArcMap a) :
    ∃ D, IsClosedDisc D ∧ range a ⊆ discInt D := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  let B : Set 𝕀 := {τ | ∃ D, IsClosedDisc D ∧ a '' Iic τ ⊆ discInt D}
  have hlow : ∀ {s t : 𝕀}, s ≤ t → t ∈ B → s ∈ B := fun h ⟨D, hD, hs⟩ =>
    ⟨D, hD, (image_mono (Iic_subset_Iic.mpr h)).trans hs⟩
  have h0 : (0 : 𝕀) ∈ B := by
    obtain ⟨D, hD, hy⟩ := exists_disc_at hT (a 0)
    refine ⟨D, hD, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have : t = 0 := le_antisymm ht t.2.1
    rwa [this]
  have hsup : sSup B ∈ B := by
    by_cases hz : sSup B = 0
    · rwa [hz]
    · refine disc_step hT ha (lt_of_le_of_ne (bot_le) (Ne.symm hz)) fun τ hτ => ?_
      obtain ⟨t, ht, hτt⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ hτ
      exact hlow hτt.le ht
  obtain ⟨D, hD, hs⟩ := id hsup
  by_cases h1 : sSup B = 1
  · refine ⟨D, hD, ?_⟩
    rw [h1] at hs
    rintro _ ⟨t, rfl⟩
    exact hs ⟨t, t.2.2, rfl⟩
  · exfalso
    have hlt : sSup B < 1 := lt_of_le_of_ne (le_top) h1
    have hV : a ⁻¹' discInt D ∈ 𝓝 (sSup B) := ha.1.continuousAt.preimage_mem_nhds
      ((isOpen_discInt hman hD).mem_nhds (hs ⟨_, self_mem_Iic, rfl⟩))
    obtain ⟨u, hu, hus⟩ := exists_Ico_subset_of_mem_nhds hV ⟨1, hlt⟩
    obtain ⟨v, hv1, hv2⟩ := exists_between hu
    have hvB : v ∈ B := by
      refine ⟨D, hD, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      rcases le_total t (sSup B) with h2 | h2
      · exact hs ⟨t, h2, rfl⟩
      · exact hus ⟨h2, lt_of_le_of_lt ht hv2⟩
    exact absurd (le_csSup (OrderTop.bddAbove _) hvB) (not_le.mpr hv1)

end GraphMinor.Surface
