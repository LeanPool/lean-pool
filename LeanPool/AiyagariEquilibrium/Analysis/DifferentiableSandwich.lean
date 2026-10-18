/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Convex.Deriv


/-!
# The Differentiable Sandwich Lemma

A function squeezed between two functions that are differentiable at a point, and agreeing
with both at that point, is itself differentiable there, with the same derivative.

This is Lemma 1 of Clausen and Strub (2020), "Reverse Calculus and Nested Optimization",
*Journal of Economic Theory* 187, 105019, and it is the foundation of their approach to
envelope theorems. Their point is that it needs neither concavity nor interiority, so it
applies where Benveniste–Scheinkman does not — in particular where a constraint binds, which
in a Bewley economy is exactly the states that matter, since the borrowing constraint is where
the whole ergodic argument lives.

The proof is two moves. The gap `U - L` is nonnegative near the point and vanishes at it, so
it has a local minimum there and its derivative is zero, which forces the two derivatives to
agree. Then the difference quotients of `F` are squeezed between those of `L` and `U`.

Mathlib has the local-minimum step (`IsLocalMin.hasDerivAt_eq_zero`) but not this lemma.
-/

@[expose] public section

open Filter Topology Asymptotics

/-- **Differentiable Sandwich Lemma** (Clausen–Strub 2020, Lemma 1). If `F` is squeezed
between `L` and `U` near `c`, all three agree at `c`, and `L` and `U` are differentiable at
`c`, then the two derivatives coincide and `F` is differentiable at `c` with that derivative. -/
theorem hasDerivAt_of_sandwich {F L U : ℝ → ℝ} {c l u : ℝ} {N : Set ℝ} (hN : N ∈ 𝓝 c)
    (hLF : ∀ x ∈ N, L x ≤ F x) (hFU : ∀ x ∈ N, F x ≤ U x)
    (hLc : L c = F c) (hUc : U c = F c)
    (hL : HasDerivAt L l c) (hU : HasDerivAt U u c) :
    l = u ∧ HasDerivAt F l c := by
  -- the gap has a local minimum at `c`, so the derivatives agree
  have hd : HasDerivAt (fun x => U x - L x) (u - l) c := hU.sub hL
  have hmin : IsLocalMin (fun x => U x - L x) c := by
    filter_upwards [hN] with x hx
    have h1 := hLF x hx
    have h2 := hFU x hx
    simp only [hLc, hUc]
    linarith
  have hul : u - l = 0 := hmin.hasDerivAt_eq_zero hd
  have hlu : l = u := by linarith
  refine ⟨hlu, ?_⟩
  -- and the difference quotients of `F` are squeezed
  have hU' : HasDerivAt U l c := by rwa [hlu]
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hA := isLittleO_iff.mp (hasDerivAt_iff_isLittleO.mp hL) hε
  have hB := isLittleO_iff.mp (hasDerivAt_iff_isLittleO.mp hU') hε
  filter_upwards [hA, hB, hN] with y hya hyb hyn
  rw [Real.norm_eq_abs] at hya hyb ⊢
  have h1 := hLF y hyn
  have h2 := hFU y hyn
  rw [abs_le] at hya hyb ⊢
  simp only [smul_eq_mul] at hya hyb ⊢
  rw [hLc] at hya
  rw [hUc] at hyb
  constructor <;> linarith [hya.1, hya.2, hyb.1, hyb.2]

/-! ### The supporting line

The upper half of the sandwich, for a concave function of one real variable. Mathlib has no
subgradient or supporting-hyperplane theory for convex or concave FUNCTIONS, but in one
dimension the slope API suffices: `ConcaveOn.slope_anti` says secant slopes through a point
are antitone, so every slope to the left is at least every slope to the right, and the
infimum of the left slopes separates them.

Clausen and Strub note that concavity is needed only for this half — the lower bound in the
sandwich need not be concave, which is where they improve on Rockafellar's antecedent. For a
value function that matters: concavity is available here, and the lazy agent's lower bound
would not have to be concave in the state.
-/

/-- **A concave function has a supporting line at any point with neighbours on both sides.**
The slope is the infimum of the secant slopes to the left. -/
theorem ConcaveOn.exists_supportingLine {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {x : ℝ} (hx : x ∈ s) (hlt : ∃ y ∈ s, y < x) (hgt : ∃ y ∈ s, x < y) :
    ∃ m : ℝ, ∀ y ∈ s, f y ≤ f x + m * (y - x) := by
  classical
  have hanti := hf.slope_anti hx
  obtain ⟨y₁, hy₁s, hy₁⟩ := hlt
  obtain ⟨y₂, hy₂s, hy₂⟩ := hgt
  -- every slope to the left dominates every slope to the right
  have hcross : ∀ z ∈ s, z < x → ∀ y ∈ s, x < y → slope f x y ≤ slope f x z := by
    intro z hzs hz y hys hy
    exact hanti ⟨hzs, by simp [ne_of_lt hz]⟩ ⟨hys, by simp [ne_of_gt hy]⟩ (le_of_lt (hz.trans hy))
  set Lset : Set ℝ := slope f x '' {y ∈ s | y < x} with hLdef
  have hne : Lset.Nonempty := ⟨slope f x y₁, ⟨y₁, ⟨hy₁s, hy₁⟩, rfl⟩⟩
  have hbdd : BddBelow Lset := by
    refine ⟨slope f x y₂, ?_⟩
    rintro _ ⟨z, ⟨hzs, hz⟩, rfl⟩
    exact hcross z hzs hz y₂ hy₂s hy₂
  refine ⟨sInf Lset, fun y hy => ?_⟩
  rcases lt_trichotomy y x with h | h | h
  · -- to the left: the slope is at least the infimum
    have hmem : slope f x y ∈ Lset := ⟨y, ⟨hy, h⟩, rfl⟩
    have hle : sInf Lset ≤ slope f x y := csInf_le hbdd hmem
    rw [slope_def_field, le_div_iff_of_neg (by linarith)] at hle
    linarith
  · subst h; simp
  · -- to the right: the slope is a lower bound for the left slopes, hence below the infimum
    have hle : slope f x y ≤ sInf Lset := by
      refine le_csInf hne ?_
      rintro _ ⟨z, ⟨hzs, hz⟩, rfl⟩
      exact hcross z hzs hz y hy h
    rw [slope_def_field, div_le_iff₀ (by linarith)] at hle
    linarith

/-- **A concave function with a differentiable lower bound touching at a point is
differentiable there**, with the lower bound's derivative.

This is the form the envelope theorem uses: concavity supplies the upper half of the sandwich
automatically, so only the lower bound has to be produced, and Clausen and Strub produce it
with the lazy agent — freeze the optimal choice and vary the state, which is differentiable
because the state then enters only through the reward. -/
theorem ConcaveOn.hasDerivAt_of_lowerBound {f L : ℝ → ℝ} {s : Set ℝ} {x l : ℝ}
    (hf : ConcaveOn ℝ s f) (hx : x ∈ s) (hs : s ∈ 𝓝 x)
    (hlt : ∃ y ∈ s, y < x) (hgt : ∃ y ∈ s, x < y)
    (hLf : ∀ y ∈ s, L y ≤ f y) (hLx : L x = f x) (hL : HasDerivAt L l x) :
    HasDerivAt f l x := by
  obtain ⟨m, hm⟩ := hf.exists_supportingLine hx hlt hgt
  have hU : HasDerivAt (fun y => f x + m * (y - x)) m x := by
    simpa using (((hasDerivAt_id x).sub_const x).const_mul m).const_add (f x)
  exact (hasDerivAt_of_sandwich hs hLf hm hLx (by simp) hL hU).2
