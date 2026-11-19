/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Local.StableSet
public import LeanPool.StableManifold.Linear.Splitting
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The stable manifold theorem for a hyperbolic fixed point

Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood of a fixed point `p` of a finite-dimensional real
normed space, with invertible and hyperbolic derivative `A = Df(p)`, and let `Eₛ`, `Eᵤ` be the
stable and unstable subspaces of `A`. Then there are a neighborhood `N` of `p` and `Cⁿ` maps
`hₛ : Eₛ → Eᵤ`, `hᵤ : Eᵤ → Eₛ`, vanishing with their derivatives at `0`, such that for every
neighborhood `U` of `p` inside `N`, the local stable set of `f|_U` is the graph `{p + x + hₛ x}`
of `hₛ` over a neighborhood of `0` in `Eₛ`, and the local unstable set of `f|_U` is the graph
`{p + y + hᵤ y}` of `hᵤ` over a neighborhood of `0` in `Eᵤ`
(`Function.exists_nhds_localStableSet_localUnstableSet_eq_graph`). The form with one open `U` and
maps `Cⁿ` near `0` is `Function.exists_localStableSet_localUnstableSet_eq_graph`.

Inside a small neighborhood of `p`, the convergence to `p` in the definitions of the local sets is
automatic: the local stable set of `f|_U` is the set of points whose forward orbit stays in `U`,
and the local unstable set the set of points having a backward orbit in `U`
(`Function.exists_nhds_localStableSet_localUnstableSet_eq_setOf`).

The unstable side is the stable side of the local inverse: `f` restricts to an open partial
homeomorphism `e` near `p` whose inverse is `Cⁿ` with derivative `A⁻¹` at `p`
(`Function.exists_openPartialHomeomorph_contDiffOn_symm`, the inverse function theorem); the
stable subspace of `A⁻¹` is the unstable subspace of `A` and conversely
(`ContinuousLinearMap.stableSubspace_symm`, `unstableSubspace_symm`), and the local unstable set
of `e|_U` is the local stable set of `e⁻¹|_U` (`Function.localStableSet_symm_eq_localUnstableSet`).
Since the local stable manifold theorem holds for every small neighborhood
(`Function.exists_localStableSet_eq_graph_of_isCompl`), one `N` serves for `f` and `e⁻¹`.

## Proofs

* `exists_openPartialHomeomorph_contDiffOn_symm`: `f` is `Cⁿ` at every point of `interior W`
  (`ContDiffOn.contDiffAt`), so the inverse function theorem
  (`ContDiffAt.toOpenPartialHomeomorph`) gives an open partial homeomorphism `e₀` with `⇑e₀ = f`
  and `p` in its source. Its source is then restricted (`OpenPartialHomeomorph.restrOpen`) to the
  points of `interior W` where `fderiv ℝ f` is invertible, an open set since `fderiv ℝ f` is
  continuous there (`ContDiffOn.continuousOn_fderiv_of_isOpen`,
  `ContinuousLinearMap.isOpen_setOfPred_isInvertible`). At each point of the target,
  `OpenPartialHomeomorph.contDiffAt_symm` makes `e.symm` of class `Cⁿ`; the argument is
  pointwise, so `n = ∞` needs no uniform neighborhood. The derivative `A⁻¹` of `e.symm` at `f p`
  comes from `HasStrictFDerivAt.to_localInverse`.
* `exists_graph_ofEq`, `exists_graphs_ofEq`: `subst`.
* `exists_nhds_localStableSet_localUnstableSet_eq_graph`: write `fderiv ℝ f p = ↑A` (`hinv`) and
  let `e` be the local inverse above. Then `e.symm` fixes `p` (`OpenPartialHomeomorph.left_inv`)
  and has derivative `A⁻¹` there (`HasFDerivAt.fderiv`), so its stable and unstable subspaces are
  `Eᵤ` and `Eₛ` (`ContinuousLinearMap.stableSubspace_symm`, `unstableSubspace_symm`),
  complementary by `isCompl_stableSubspace_unstableSubspace` and `IsCompl.symm`. Apply
  `exists_localStableSet_eq_graph_of_isCompl` to `f` (radius `δ₁`, map `hₛ`) and to `e.symm` on
  `e.target` (radius `δ₂`, map `hᵤ`), and take `N = ball p (min δ₁ δ₂) ∩ e.source ∩ e.target`, a
  neighborhood of `p`. The stable side follows at once. For the unstable side and `U ⊆ N`,
  `localUnstableSet f p U = localUnstableSet e p U` (`Function.localUnstableSet_congr`, as
  `⇑e = f`) `= localStableSet e.symm p U` (`Function.localStableSet_symm_eq_localUnstableSet`, as
  `U ⊆ e.source ∩ e.target`), the graph of `hᵤ` over a neighborhood of `0` in the stable subspace
  of `fderiv ℝ e.symm p`; `exists_graphs_ofEq` makes `hᵤ`, once for all `U`, a map from `Eᵤ` to
  `Eₛ`.
* `exists_localStableSet_localUnstableSet_eq_graph`: the previous theorem with `U = interior N`,
  open and a neighborhood of `p` (`interior_mem_nhds`), and `ContDiff.contDiffOn`.
* `exists_nhds_localStableSet_localUnstableSet_eq_setOf`: the same `e` and
  `exists_localStableSet_eq_setOf_forall_iterate_mem` for `f` and for `e.symm`, on
  `N = ball p (min δ₁ δ₂) ∩ e.source ∩ e.target`. For `U ⊆ N`, the local unstable set of `f` is
  the local stable set of `e.symm`, the set of points whose `e.symm`-orbit stays in `U`, that is,
  the set of points having a backward `e`-orbit in `U`
  (`Function.setOf_forall_iterate_symm_mem_eq`).
-/

@[expose] public section

open Filter Topology Metric Set

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The local inverse** of a `Cⁿ` map with invertible derivative `A` at `p` (`1 ≤ n ≤ ∞`): an
open partial homeomorphism `e` with `⇑e = f` and `p` in its source, whose inverse is `Cⁿ` on its
target and has derivative `A⁻¹` at `f p`.

Proof: the inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`), with the source
restricted to the points where `f` is `Cⁿ` with invertible derivative, and
`OpenPartialHomeomorph.contDiffAt_symm` at each point of the target. -/
theorem exists_openPartialHomeomorph_contDiffOn_symm {f : E → E} {p : E} {W : Set E} {n : ℕ∞}
    (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) {A : E ≃L[ℝ] E}
    (hA : fderiv ℝ f p = A) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧ p ∈ e.source ∧
      ContDiffOn ℝ n e.symm e.target ∧ HasFDerivAt e.symm (A.symm : E →L[ℝ] E) (f p) := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    have : (0 : ℕ∞) < n := zero_lt_one.trans_le hn
    exact_mod_cast this.ne'
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hfa (x : E) (hx : x ∈ interior W) : ContDiffAt ℝ n f x :=
    hf.contDiffAt (mem_interior_iff_mem_nhds.1 hx)
  have hfd (x : E) (hx : x ∈ interior W) : HasFDerivAt f (fderiv ℝ f x) x :=
    ((hfa x hx).differentiableAt hn0).hasFDerivAt
  have hpW : p ∈ interior W := mem_interior_iff_mem_nhds.2 hW
  have hfp : HasFDerivAt f (A : E →L[ℝ] E) p := hA ▸ hfd p hpW
  -- the inverse function theorem, then restriction to the points with invertible derivative
  let e₀ := (hfa p hpW).toOpenPartialHomeomorph f hfp hn0
  have hT : IsOpen (interior W ∩ fderiv ℝ f ⁻¹' {T | T.IsInvertible}) :=
    ((hf.mono interior_subset).continuousOn_fderiv_of_isOpen isOpen_interior
      hn1).isOpen_inter_preimage isOpen_interior
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let e := e₀.restrOpen _ hT
  have hpe : p ∈ e.source :=
    ⟨(hfa p hpW).mem_toOpenPartialHomeomorph_source hfp hn0, hpW, A, hA.symm⟩
  refine ⟨e, rfl, hpe, fun y hy ↦ ?_, ?_⟩
  · obtain ⟨-, hxW, M, hM⟩ := e.map_target hy
    refine (e.contDiffAt_symm hy (f₀' := M) ?_ (hfa _ hxW)).contDiffWithinAt
    rw [hM]
    exact hfd _ hxW
  · exact ((hfa p hpW).hasStrictFDerivAt' hfp hn0).to_localInverse.hasFDerivAt

omit [FiniteDimensional ℝ E] in
/-- A graph over a subspace is a graph over any equal subspace (to move between the subspaces of
`A⁻¹` and those of `A`, equal but not definitionally). -/
theorem exists_graph_ofEq {K₁ K₂ L₁ L₂ : Submodule ℝ E} (h₁ : K₁ = L₁) (h₂ : K₂ = L₂) {n : ℕ∞}
    {p : E} {s : Set E} {V : Set K₁} (hV : V ∈ 𝓝 0) {h : K₁ → K₂} (hh : ContDiffOn ℝ n h V)
    (h0 : h 0 = 0) (hd : fderiv ℝ h 0 = 0) (hs : s = (fun x ↦ p + ↑x + ↑(h x)) '' V) :
    ∃ V' ∈ 𝓝 (0 : L₁), ∃ h' : L₁ → L₂, ContDiffOn ℝ n h' V' ∧ h' 0 = 0 ∧ fderiv ℝ h' 0 = 0 ∧
      s = (fun x ↦ p + ↑x + ↑(h' x)) '' V' := by
  subst h₁ h₂
  exact ⟨V, hV, h, hh, h0, hd, hs⟩

omit [FiniteDimensional ℝ E] in
/-- A family of graphs of one map over a subspace is a family of graphs of one map over any equal
subspace: `exists_graph_ofEq` for all the sets `s U` with `Q U` at once. -/
theorem exists_graphs_ofEq {K₁ K₂ L₁ L₂ : Submodule ℝ E} (h₁ : K₁ = L₁) (h₂ : K₂ = L₂)
    {n : ℕ∞} {p : E} {Q : Set E → Prop} {s : Set E → Set E} {h : K₁ → K₂}
    (hh : ContDiff ℝ n h) (h0 : h 0 = 0) (hd : fderiv ℝ h 0 = 0)
    (hs : ∀ U, Q U → ∃ V ∈ 𝓝 (0 : K₁), s U = (fun x ↦ p + ↑x + ↑(h x)) '' V) :
    ∃ h' : L₁ → L₂, ContDiff ℝ n h' ∧ h' 0 = 0 ∧ fderiv ℝ h' 0 = 0 ∧
      ∀ U, Q U → ∃ V ∈ 𝓝 (0 : L₁), s U = (fun x ↦ p + ↑x + ↑(h' x)) '' V := by
  subst h₁ h₂
  exact ⟨h, hh, h0, hd, hs⟩

/-- At a fixed point with invertible derivative, the local inverse `e` of `f` fixes `p`, and the
stable and unstable subspaces of the derivative of `e⁻¹` at `p` are those of `Df(p)` exchanged. -/
private lemma exists_localInverse_of_isInvertible {f : E → E} {p : E} {W : Set E} {n : ℕ∞}
    (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧ p ∈ e.source ∧ p ∈ e.target ∧
      ContDiffOn ℝ n e.symm e.target ∧ e.symm p = p ∧
      (fderiv ℝ e.symm p).stableSubspace = (fderiv ℝ f p).unstableSubspace ∧
      (fderiv ℝ e.symm p).unstableSubspace = (fderiv ℝ f p).stableSubspace := by
  obtain ⟨A, hA⟩ := hinv
  obtain ⟨e, he, hpe, hes, hed⟩ := exists_openPartialHomeomorph_contDiffOn_symm hn hW hf hA.symm
  have hep : e p = p := by rw [he, hfix]
  have hgd : fderiv ℝ e.symm p = (A.symm : E →L[ℝ] E) := by
    rw [hfix] at hed
    exact hed.fderiv
  refine ⟨e, he, hpe, hep ▸ e.map_source hpe, hes, by simpa [hep] using e.left_inv hpe, ?_, ?_⟩
  · rw [hgd, ContinuousLinearMap.stableSubspace_symm, hA]
  · rw [hgd, ContinuousLinearMap.unstableSubspace_symm, hA]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For `U` inside the source and the target of the local inverse `e` of `f`, the local unstable
set of `f|_U` is the local stable set of `e⁻¹|_U`. -/
private lemma localUnstableSet_eq_localStableSet_symm {f : E → E} {p : E}
    {e : OpenPartialHomeomorph E E} (he : (e : E → E) = f) {U : Set E}
    (hU : U ⊆ e.source ∩ e.target) :
    localUnstableSet f p U = localStableSet e.symm p U := by
  rw [localUnstableSet_congr (g := e) fun x _ ↦ by rw [he]]
  exact (localStableSet_symm_eq_localUnstableSet e hU).1.symm

/-- **The stable manifold theorem** for maps, in graph form, for every small neighborhood (Irwin,
*Smooth Dynamical Systems*, Chapter 6; Hirsch, Pugh and Shub, *Invariant Manifolds*; Shub, *Global
Stability of Dynamical Systems*). Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood `W` of a fixed
point `p`, with invertible and hyperbolic derivative `A = Df(p)` (`f` is a local diffeomorphism at
`p`), and let `E_s`, `E_u` be the stable and unstable subspaces of `A`. Then there are a
neighborhood `N` of `p` and `Cⁿ` maps `h_s : E_s → E_u`, `h_u : E_u → E_s`, vanishing with their
derivatives at `0`, such that for every neighborhood `U` of `p` inside `N`

* the local stable set of `f|_U` is the graph `{p + x + h_s(x)}` of `h_s` over a neighborhood
  `V_s` of `0` in `E_s` (near `p`, a `Cⁿ` embedded submanifold tangent at `p` to `E_s`), and
* the local unstable set of `f|_U` is the graph `{p + y + h_u(y)}` of `h_u` over a neighborhood
  `V_u` of `0` in `E_u` (near `p`, a `Cⁿ` embedded submanifold tangent at `p` to `E_u`).

The maps do not depend on `U`; the neighborhoods `V_s`, `V_u` do.

Proof: `exists_localStableSet_eq_graph_of_isCompl` for `f` and for its local inverse
(`exists_openPartialHomeomorph_contDiffOn_symm`), on a common neighborhood `N`, with
`localStableSet_symm_eq_localUnstableSet` and `stableSubspace_symm`, `unstableSubspace_symm`. -/
theorem exists_nhds_localStableSet_localUnstableSet_eq_graph {f : E → E} {p : E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ N ∈ 𝓝 p,
      ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
        ContDiff ℝ n hs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
      ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
        ContDiff ℝ n hu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
      ∀ U ∈ 𝓝 p, U ⊆ N →
        (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
        (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
          localUnstableSet f p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu) := by
  obtain ⟨e, he, hpe, hpt, hes, hgp, hst, hun⟩ :=
    exists_localInverse_of_isInvertible hn hW hf hfix hinv
  have hsplit := ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace hyp
  -- the local stable manifold theorem for `f` and for `e⁻¹`
  obtain ⟨δ₁, hδ₁, hs, hsC, hs0, hsd, hsU⟩ :=
    exists_localStableSet_eq_graph_of_isCompl hn hW hf hfix hsplit
  obtain ⟨δ₂, hδ₂, hu, huC, hu0, hud, huU⟩ :=
    exists_localStableSet_eq_graph_of_isCompl hn (e.open_target.mem_nhds hpt) hes hgp
      (by rw [hst, hun]; exact hsplit.symm)
  -- one neighborhood for both
  set N := ball p (min δ₁ δ₂) ∩ e.source ∩ e.target
  have hN : N ∈ 𝓝 p := ((isOpen_ball.inter e.open_source).inter e.open_target).mem_nhds
    ⟨⟨mem_ball_self (lt_min hδ₁ hδ₂), hpe⟩, hpt⟩
  -- the unstable side, as a graph over `Eᵤ` with values in `Eₛ`
  obtain ⟨hu', hu'C, hu'0, hu'd, hu'U⟩ := exists_graphs_ofEq hst hun huC hu0 hud
    (Q := fun U ↦ U ∈ 𝓝 p ∧ U ⊆ N) (s := fun U ↦ localUnstableSet f p U) fun U ⟨hU, hUN⟩ ↦ by
      rw [localUnstableSet_eq_localStableSet_symm he fun x hx ↦ ⟨(hUN hx).1.2, (hUN hx).2⟩]
      exact huU U hU fun x hx ↦ ball_subset_ball (min_le_right _ _) (hUN hx).1.1
  refine ⟨N, hN, hs, hsC, hs0, hsd, hu', hu'C, hu'0, hu'd, fun U hU hUN ↦
    ⟨hsU U hU fun x hx ↦ ball_subset_ball (min_le_left _ _) (hUN hx).1.1, hu'U U ⟨hU, hUN⟩⟩⟩

/-- **The stable manifold theorem** for maps, in graph form, for one neighborhood (Irwin, *Smooth
Dynamical Systems*, Chapter 6; Hirsch, Pugh and Shub, *Invariant Manifolds*; Shub, *Global
Stability of Dynamical Systems*). Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood `W` of a fixed
point `p`, with invertible and hyperbolic derivative `A = Df(p)` (`f` is a local diffeomorphism at
`p`), and let `E_s`, `E_u` be the stable and unstable subspaces of `A`. Then there are an open
neighborhood `U` of `p` and `Cⁿ` maps `h_s : E_s → E_u`, `h_u : E_u → E_s`, vanishing with their
derivatives at `0`, such that

* the local stable set of `f|_U` is the graph `{p + x + h_s(x)}` of `h_s` over a neighborhood
  `V_s` of `0` in `E_s` (near `p`, a `Cⁿ` embedded submanifold tangent at `p` to `E_s`), and
* the local unstable set of `f|_U` is the graph `{p + y + h_u(y)}` of `h_u` over a neighborhood
  `V_u` of `0` in `E_u` (near `p`, a `Cⁿ` embedded submanifold tangent at `p` to `E_u`).

Proof: `exists_nhds_localStableSet_localUnstableSet_eq_graph`, with `U = interior N`. -/
theorem exists_localStableSet_localUnstableSet_eq_graph {f : E → E} {p : E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ U ∈ 𝓝 p, IsOpen U ∧
      (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
        ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
          ContDiffOn ℝ n hs Vs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
      (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
        ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
          ContDiffOn ℝ n hu Vu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
          localUnstableSet f p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu) := by
  obtain ⟨N, hN, hs, hsC, hs0, hsd, hu, huC, hu0, hud, hNU⟩ :=
    exists_nhds_localStableSet_localUnstableSet_eq_graph hn hW hf hfix hinv hyp
  have hU : interior N ∈ 𝓝 p := interior_mem_nhds.2 hN
  obtain ⟨⟨Vs, hVs, hsU⟩, ⟨Vu, hVu, huU⟩⟩ := hNU (interior N) hU interior_subset
  exact ⟨interior N, hU, isOpen_interior, ⟨Vs, hVs, hs, hsC.contDiffOn, hs0, hsd, hsU⟩,
    ⟨Vu, hVu, hu, huC.contDiffOn, hu0, hud, huU⟩⟩

/-- **Convergence is automatic in the local sets**: under the hypotheses of the stable manifold
theorem, there is a neighborhood `N` of `p` such that for every set `U` inside `N`, the local
stable set of `f|_U` is the set of points whose forward orbit stays in `U`, and the local unstable
set of `f|_U` is the set of points having a backward orbit in `U` (`y 0 = x`,
`f (y (k + 1)) = y k`). So leaving the convergence to `p` out of the definitions of the local sets
changes nothing.

Proof: `exists_localStableSet_eq_setOf_forall_iterate_mem` for `f` and for its local inverse, and
`setOf_forall_iterate_symm_mem_eq`. -/
theorem exists_nhds_localStableSet_localUnstableSet_eq_setOf {f : E → E} {p : E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ N ∈ 𝓝 p, ∀ U ⊆ N,
      localStableSet f p U = {x | ∀ k, f^[k] x ∈ U} ∧
      localUnstableSet f p U = {x | ∃ y : ℕ → E, y 0 = x ∧ ∀ k, y k ∈ U ∧ f (y (k + 1)) = y k} := by
  obtain ⟨e, he, hpe, hpt, hes, hgp, hst, hun⟩ :=
    exists_localInverse_of_isInvertible hn hW hf hfix hinv
  have hsplit := ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace hyp
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_localStableSet_eq_setOf_forall_iterate_mem hn hW hf hfix hsplit
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_localStableSet_eq_setOf_forall_iterate_mem hn
    (e.open_target.mem_nhds hpt) hes hgp (by rw [hst, hun]; exact hsplit.symm)
  refine ⟨ball p (min δ₁ δ₂) ∩ e.source ∩ e.target,
    ((isOpen_ball.inter e.open_source).inter e.open_target).mem_nhds
      ⟨⟨mem_ball_self (lt_min hδ₁ hδ₂), hpe⟩, hpt⟩, fun U hU ↦
    ⟨h₁ U fun x hx ↦ ball_subset_ball (min_le_left _ _) (hU hx).1.1, ?_⟩⟩
  have hUe : U ⊆ e.source ∩ e.target := fun x hx ↦ ⟨(hU hx).1.2, (hU hx).2⟩
  rw [localUnstableSet_eq_localStableSet_symm he hUe,
    h₂ U fun x hx ↦ ball_subset_ball (min_le_right _ _) (hU hx).1.1,
    setOf_forall_iterate_symm_mem_eq e hUe, he]

end Function
