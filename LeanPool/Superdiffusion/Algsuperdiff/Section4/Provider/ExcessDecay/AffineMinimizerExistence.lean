/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.AffineExcess
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# AffineMinimizerExistence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Attainment of the affine minimum `ℓ(u,W)` (the `min`/`argmin`)

`e.excess.def` writes the excess with a **`min`** over the affine functions and
names the minimizer `ℓ(u,W) = argmin`.  `AffineExcess.lean` defines the excess as
the `sInf` of the same competitor set.  This module supplies the attainment
statement --- the assertion that the `sInf` is a `min` --- by the direct method in
the `(d+1)`-dimensional affine parameter space `ℝ × Vec d`.

## What is proved, and on which class

`exists_isAffineMinimizer_of_nondegenerate` proves attainment on every window `W`
for which

* `u ∈ L²(W)` and every affine function is in `L²(W)` (`haff`), and
* the affine evaluation map is **two-sidedly nondegenerate** on `W`:
  `c₀‖(c,g)‖ ≤ ‖c + g·x‖_{L²(W)} ≤ K‖(c,g)‖` with `c₀ > 0` (`hlb`, `hub`).

That is exactly the hypothesis set the direct method needs: `hub` gives that the
competitor function is `K`-Lipschitz, hence continuous; `hlb` gives coercivity;
`ℝ × Vec d` is finite-dimensional, hence proper, so a continuous coercive function
attains a global minimum, and a global minimizer of the competitor function
realizes the `sInf`.

Note also that `hlb` *forces* `0 < |W|`.

## The residual, stated precisely (attainment on the consumption class)

The §4.3 consumption sites are **not** the source's "bounded domains": they are
the truncated windows `U_j = (x + □_j) ∩ □_m` and the abstract nested family of
`l.iteration.lemma`, whose only stated geometry is the sandwich `x + □_{j-2} ⊆
U_j ⊆ y + □_j` (hypothesis (iii), scoped to `j ≤ m` per the binding).  On such
a window `hlb`/`hub` are *theorems*, not assumptions, and the route is fixed
and known:

* `hub` follows from `W ⊆ y + □_j` and the crude bound
  `|c + g·x| ≤ |c| + |g| · diam`, since `‖·‖_{L²(W)}` of a bounded function is at
  most its sup;

Until it is proved, every §4.3 statement in this tree is phrased so that a
*chosen* minimizer's data `(c_j, g_j)` is **quantified**, never obtained from a
`choose` on an unavailable attainment: see `IterationLemma.lean`, whose slope
sequence `p` is a parameter and whose hypotheses are properties of the given
minimizers.

## References

* ABK26, `e.excess.def`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory Filter
open HCPolySupport (Vec)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- **Attainment of the affine minimum, on a nondegenerate window.**

On a window carrying the two-sided affine nondegeneracy `hlb`/`hub` and on
which `u` is square-integrable, the infimum defining `affineExcessRaw` is
attained: some affine parameter pair `(c, g)` is an `IsAffineMinimizer`.  This
is the source's `min`/`argmin`, with the hypotheses the statement needs made
visible.  See the module docstring for the (false) hypothesis-free reading and
for the residual on the truncated consumption windows. -/
theorem exists_isAffineMinimizer_of_nondegenerate {W : Set (Vec d)} {c₀ K : ℝ}
    (hc₀ : 0 < c₀)
    (haff : ∀ (c : ℝ) (g : Vec d), MemLp (affineEval c g) 2 (volume.restrict W))
    (hlb : ∀ (c : ℝ) (g : Vec d),
      c₀ * ‖((c, g) : ℝ × Vec d)‖ ≤ normalizedL2On W (affineEval c g))
    (hub : ∀ (c : ℝ) (g : Vec d),
      normalizedL2On W (affineEval c g) ≤ K * ‖((c, g) : ℝ × Vec d)‖)
    (u : Vec d → ℝ) (hu : MemLp u 2 (volume.restrict W)) :
    ∃ (c : ℝ) (g : Vec d), IsAffineMinimizer W u c g := by
  classical
  set F : ℝ × Vec d → ℝ := fun p => affineDistOn W u p.1 p.2 with hFdef
  have hK0 : 0 ≤ K := by
    have h := hub 1 0
    have hn : ‖((1, (0 : Vec d)) : ℝ × Vec d)‖ = 1 := by
      simp [Prod.norm_def]
    rw [hn, mul_one] at h
    exact le_trans (normalizedL2On_nonneg _ _) h
  -- Step 1: the competitor function is `K`-Lipschitz.
  have hsplit : ∀ a b : ℝ × Vec d,
      F a ≤ F b + normalizedL2On W (affineEval (b.1 - a.1) (b.2 - a.2)) := by
    intro a b
    have hpt : (fun x => u x - affineEval a.1 a.2 x)
        = fun x => (u x - affineEval b.1 b.2 x) + affineEval (b.1 - a.1) (b.2 - a.2) x := by
      funext x
      rw [← affineEval_sub]
      ring
    have hmem : MemLp (fun x => u x - affineEval b.1 b.2 x) 2 (volume.restrict W) :=
      hu.sub (haff b.1 b.2)
    have hmink := normalizedL2On_add_le (W := W)
      (f := fun x => u x - affineEval b.1 b.2 x)
      (g := affineEval (b.1 - a.1) (b.2 - a.2)) hmem (haff _ _)
    have hFa : F a = normalizedL2On W fun x => u x - affineEval a.1 a.2 x := rfl
    have hFb : F b = normalizedL2On W fun x => u x - affineEval b.1 b.2 x := rfl
    rw [hFa, hpt, hFb]
    exact hmink
  have hLip : ∀ p q : ℝ × Vec d, |F p - F q| ≤ K * ‖p - q‖ := by
    intro p q
    have hpq : ((q.1 - p.1, q.2 - p.2) : ℝ × Vec d) = q - p := rfl
    have hqp : ((p.1 - q.1, p.2 - q.2) : ℝ × Vec d) = p - q := rfl
    have h1 : F p ≤ F q + K * ‖p - q‖ := by
      have hsp := hsplit p q
      have hb := hub (q.1 - p.1) (q.2 - p.2)
      rw [hpq, norm_sub_rev q p] at hb
      linarith only [hsp, hb]
    have h2 : F q ≤ F p + K * ‖p - q‖ := by
      have hsp := hsplit q p
      have hb := hub (p.1 - q.1) (p.2 - q.2)
      rw [hqp] at hb
      linarith only [hsp, hb]
    rw [abs_le]
    exact ⟨by linarith only [h1, h2], by linarith only [h1, h2]⟩
  have hcont : Continuous F := by
    have hlip : LipschitzWith (Real.toNNReal K) F := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro p q
      rw [Real.dist_eq, dist_eq_norm]
      calc |F p - F q| ≤ K * ‖p - q‖ := hLip p q
        _ = (K.toNNReal : ℝ) * ‖p - q‖ := by rw [Real.coe_toNNReal _ hK0]
    exact hlip.continuous
  -- Step 2: coercivity.
  have hcoer : ∀ p : ℝ × Vec d, c₀ * ‖p‖ - normalizedL2On W u ≤ F p := by
    intro p
    have hpt : (fun x => (affineEval p.1 p.2 x - u x) + u x) = affineEval p.1 p.2 := by
      funext x; ring
    have hmem : MemLp (fun x => affineEval p.1 p.2 x - u x) 2 (volume.restrict W) :=
      (haff p.1 p.2).sub hu
    have hmink := normalizedL2On_add_le (W := W)
      (f := fun x => affineEval p.1 p.2 x - u x) (g := u) hmem hu
    rw [hpt] at hmink
    have hsym : normalizedL2On W (fun x => affineEval p.1 p.2 x - u x)
        = normalizedL2On W fun x => u x - affineEval p.1 p.2 x :=
      normalizedL2On_sub_comm W _ _
    rw [hsym] at hmink
    have hlbp : c₀ * ‖((p.1, p.2) : ℝ × Vec d)‖
        ≤ normalizedL2On W (affineEval p.1 p.2) := hlb p.1 p.2
    have hpeta : ((p.1, p.2) : ℝ × Vec d) = p := rfl
    rw [hpeta] at hlbp
    have hFp : F p = normalizedL2On W fun x => u x - affineEval p.1 p.2 x := rfl
    rw [hFp]
    linarith only [hmink, hlbp]
  -- Step 3: the direct method on the proper space `ℝ × Vec d`.
  have hF0 : F 0 = normalizedL2On W u := by
    have hpt : (fun x => u x - affineEval (0 : ℝ) (0 : Vec d) x) = u := by
      funext x
      rw [affineEval_zero]
      ring
    change normalizedL2On W (fun x => u x - affineEval (0 : ℝ) (0 : Vec d) x)
      = normalizedL2On W u
    rw [hpt]
  obtain ⟨p, hp⟩ : ∃ p : ℝ × Vec d, ∀ q : ℝ × Vec d, F p ≤ F q := by
    refine hcont.exists_forall_le' (0 : ℝ × Vec d) ?_
    have hcc : ∀ᶠ q in cocompact (ℝ × Vec d),
        (2 * normalizedL2On W u + 1) / c₀ ≤ ‖q‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hcc] with q hq
    have h1 : c₀ * ‖q‖ - normalizedL2On W u ≤ F q := hcoer q
    have h2 : c₀ * ((2 * normalizedL2On W u + 1) / c₀) ≤ c₀ * ‖q‖ :=
      mul_le_mul_of_nonneg_left hq hc₀.le
    have h3 : c₀ * ((2 * normalizedL2On W u + 1) / c₀) = 2 * normalizedL2On W u + 1 := by
      field_simp
    rw [hF0]
    linarith only [h1, h2, h3]
  -- Step 4: a global minimizer realizes the infimum.
  refine ⟨p.1, p.2, ?_⟩
  change affineDistOn W u p.1 p.2 = affineExcessRaw W u
  refine le_antisymm ?_ (affineExcessRaw_le_affineDistOn W u p.1 p.2)
  refine le_csInf (affineDistSet_nonempty W u) ?_
  rintro y ⟨q, rfl⟩
  exact hp q

end

end Algsuperdiff.Section4.Provider.ExcessDecay
