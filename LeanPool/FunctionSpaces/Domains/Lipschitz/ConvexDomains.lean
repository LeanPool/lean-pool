/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.LocalLipschitzGraphs

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Bounded open convex sets are bounded Lipschitz domains

Let `Ω` be a bounded open convex set with `‖x‖ ≤ C` on `Ω`, let `B(a, δ) ⊆ Ω` and let `ν` be a
unit vector. The **ray length** `ℓ(y) = sup {s : a + y - s ν ∈ Ω}` (`Rd.rayLength`) is the length
of the ray from `a + y` in the direction `-ν` inside `Ω`.

* For `a + y ∈ Ω` and `s ≥ 0`, the point `a + y - s ν` lies in `Ω` iff `s < ℓ(y)`
  (`Rd.mem_iff_lt_rayLength`), by openness and convexity.
* The cone estimate: on the ball of radius `δ/4`, `ℓ` is `4C/δ`-Lipschitz
  (`Rd.rayLength_le_rayLength_add`, `Rd.lipschitzOnWith_rayLength`), since the convex hull of a ray
  and the ball `B(a, δ)` contains the shortened rays from nearby starting points.
* At a frontier point `z`, with `ν = (a - z)/‖a - z‖`, the set `Ω` agrees near `z` with the region
  above the graph of `y ↦ ‖a - z‖ - ℓ(y)` over `ν^⊥` (`Rd.mem_iff_sub_rayLength_lt`). McShane's
  extension (`Rd.isLipschitzDomainAt_of_lipschitzOnWith`) then makes `Ω` Lipschitz near `z`
  (`Rd.isLipschitzDomainAt_of_convex`). Every open convex set, bounded or not, is Lipschitz near
  each frontier point, since it agrees near `z` with its intersection with `B(z, 1)`
  (`Rd.isLipschitzDomainAt_of_convex_of_isOpen`).

Hence every bounded open convex set is a bounded Lipschitz set
(`Rd.isBoundedLipschitzDomain_of_convex`; Grisvard, Corollary 1.2.2.3) and, in finite
dimension, the carrier of a `Rd.BoundedLipschitzDomain` (`Rd.BoundedLipschitzDomain.ofConvex`);
the open unit cube `(0, 1)^n` is an example (`Rd.isBoundedLipschitzDomain_unitCube`,
`Rd.BoundedLipschitzDomain.unitCube`). It is convex and nonempty (`Rd.convex_unitCube`,
`Rd.nonempty_unitCube`), and its closure is the closed unit cube `[0, 1]^n`
(`Rd.closure_unitCube`).
-/

@[expose] public section

open Metric Set

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The ray length -/

/-- The **ray length** `ℓ(y) = sup {s ∈ ℝ : a + y - s ν ∈ Ω}`: for a bounded convex open set `Ω`, a
point `a + y ∈ Ω` and a unit vector `ν`, the length of the ray from `a + y` in the direction `-ν`
inside `Ω` (`Rd.mem_iff_lt_rayLength`). Lean's supremum of a set that is empty or unbounded above
is `0`. -/
noncomputable def rayLength (Ω : Set V) (a ν y : V) : ℝ :=
  sSup {s : ℝ | a + y - s • ν ∈ Ω}

variable {Ω : Set V} {a ν : V} {C : ℝ}

/-- **The ray from a point of `Ω` meets `Ω`**: if `a + y ∈ Ω`, the set of parameters `s` with
`a + y - s ν ∈ Ω` contains `s = 0`. -/
theorem nonempty_raySet {y : V} (hy : a + y ∈ Ω) : {s : ℝ | a + y - s • ν ∈ Ω}.Nonempty :=
  ⟨0, by simpa using hy⟩

/-- **Points of a ray in a bounded set**: if `‖x‖ ≤ C` on `Ω`, `‖ν‖ = 1` and `a + y - s ν ∈ Ω`, then
`s ≤ ‖a + y‖ + C`, by the triangle inequality for `s ν = (a + y) - (a + y - s ν)`. -/
theorem le_norm_add_of_sub_smul_mem (hC : ∀ x ∈ Ω, ‖x‖ ≤ C) (hν : ‖ν‖ = 1) {y : V} {s : ℝ}
    (hs : a + y - s • ν ∈ Ω) : s ≤ ‖a + y‖ + C := by
  have h : ‖s • ν‖ ≤ ‖a + y‖ + ‖a + y - s • ν‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le (a + y) (a + y - s • ν)
  rw [norm_smul, hν, mul_one, Real.norm_eq_abs] at h
  linarith [le_abs_self s, hC _ hs]

/-- In a bounded set `Ω` and for a unit vector `ν`, the parameters `s` with `a + y - s ν ∈ Ω` are
bounded above (`Rd.le_norm_add_of_sub_smul_mem`), so the supremum in `Rd.rayLength` is a genuine
one. -/
theorem bddAbove_rayLength (hC : ∀ x ∈ Ω, ‖x‖ ≤ C) (hν : ‖ν‖ = 1) (y : V) :
    BddAbove {s : ℝ | a + y - s • ν ∈ Ω} :=
  ⟨‖a + y‖ + C, fun _ hs => le_norm_add_of_sub_smul_mem hC hν hs⟩

/-- In a bounded set `Ω` and for a unit vector `ν`, every `s` with `a + y - s ν ∈ Ω` is at most
the ray length. -/
theorem le_rayLength (hC : ∀ x ∈ Ω, ‖x‖ ≤ C) (hν : ‖ν‖ = 1) {y : V} {s : ℝ}
    (hs : a + y - s • ν ∈ Ω) : s ≤ rayLength Ω a ν y :=
  le_csSup (bddAbove_rayLength hC hν y) hs

/-- **The ray length is at most `2C`** when `a + y ∈ Ω`, `‖x‖ ≤ C` on `Ω` and `ν` is a unit
vector: every admissible `s` satisfies `s ≤ ‖a + y‖ + C ≤ 2C`. -/
theorem rayLength_le (hC : ∀ x ∈ Ω, ‖x‖ ≤ C) (hν : ‖ν‖ = 1) {y : V} (hy : a + y ∈ Ω) :
    rayLength Ω a ν y ≤ 2 * C :=
  csSup_le (nonempty_raySet hy) fun _ hs => by
    linarith [le_norm_add_of_sub_smul_mem hC hν hs, hC _ hy]

/-- **The ray inside a convex open set**: if `Ω` is convex, open and bounded, `‖ν‖ = 1`,
`a + y ∈ Ω` and `s ≥ 0`, then `a + y - s ν ∈ Ω` iff `s < ℓ(y)`. Openness moves a little further
along the ray; convexity fills the segment between `a + y` and a point `a + y - b ν ∈ Ω` with
`b > s` (Mathlib's `exists_lt_of_lt_csSup`). -/
theorem mem_iff_lt_rayLength (hΩ : Convex ℝ Ω) (ho : IsOpen Ω) (hC : ∀ x ∈ Ω, ‖x‖ ≤ C)
    (hν : ‖ν‖ = 1) {y : V} (hy : a + y ∈ Ω) {s : ℝ} (hs : 0 ≤ s) :
    a + y - s • ν ∈ Ω ↔ s < rayLength Ω a ν y := by
  constructor
  · intro h
    have hcont : Continuous fun t : ℝ => a + y - t • ν := by fun_prop
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (ho.preimage hcont) s h
    have hmem : a + y - (s + ε / 2) • ν ∈ Ω := hball (by
      rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      linarith)
    linarith [le_rayLength hC hν hmem]
  · intro h
    obtain ⟨b, hb, hsb⟩ :=
      exists_lt_of_lt_csSup (nonempty_raySet hy) h
    have hb0 : 0 < b := hs.trans_lt hsb
    have heq : a + y - s • ν = (1 - s / b) • (a + y) + (s / b) • (a + y - b • ν) := by
      rw [smul_sub (s / b), smul_smul, div_mul_cancel₀ s hb0.ne']
      module
    rw [heq]
    exact hΩ hy hb (by rw [sub_nonneg, div_le_one hb0]; exact hsb.le) (div_nonneg hs hb0.le)
      (by ring)

/-! ### The cone estimate -/

/-- **The cone estimate for convex sets**: let `Ω` be convex with `B(a, δ) ⊆ Ω`,
`‖y₁‖, ‖y₂‖ < δ/4` and `μ = 2‖y₁ - y₂‖/δ`. If `a + y₁ - s ν ∈ Ω`, then
`a + y₂ - (1 - μ) s ν ∈ Ω`: it is the convex combination
`(1 - μ)(a + y₁ - s ν) + μ (a + b)` with `b = y₁ + μ⁻¹ (y₂ - y₁)`, and `‖b‖ < δ/4 + δ/2 < δ`. -/
theorem sub_smul_mem_of_norm_lt (hΩ : Convex ℝ Ω) {δ : ℝ} (hδ : 0 < δ) (hball : ball a δ ⊆ Ω)
    {y₁ y₂ : V} (h₁ : ‖y₁‖ < δ / 4) (h₂ : ‖y₂‖ < δ / 4) {s : ℝ} (hs : a + y₁ - s • ν ∈ Ω) :
    a + y₂ - ((1 - 2 * ‖y₁ - y₂‖ / δ) * s) • ν ∈ Ω := by
  rcases eq_or_ne y₁ y₂ with rfl | hne
  · simpa using hs
  have hn : 0 < ‖y₁ - y₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hμ : 0 < 2 * ‖y₁ - y₂‖ / δ := by positivity
  have hμ1 : 2 * ‖y₁ - y₂‖ / δ ≤ 1 := by
    rw [div_le_one hδ]
    linarith [norm_sub_le y₁ y₂]
  have hb : a + (y₁ + (2 * ‖y₁ - y₂‖ / δ)⁻¹ • (y₂ - y₁)) ∈ Ω := by
    refine hball (add_mem_ball_iff_norm.2 ?_)
    calc ‖y₁ + (2 * ‖y₁ - y₂‖ / δ)⁻¹ • (y₂ - y₁)‖
        ≤ ‖y₁‖ + (2 * ‖y₁ - y₂‖ / δ)⁻¹ * ‖y₁ - y₂‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_inv, Real.norm_of_nonneg hμ.le, norm_sub_rev]
      _ = ‖y₁‖ + δ / 2 := by field_simp
      _ < δ := by linarith
  have heq : a + y₂ - ((1 - 2 * ‖y₁ - y₂‖ / δ) * s) • ν =
      (1 - 2 * ‖y₁ - y₂‖ / δ) • (a + y₁ - s • ν) +
        (2 * ‖y₁ - y₂‖ / δ) • (a + (y₁ + (2 * ‖y₁ - y₂‖ / δ)⁻¹ • (y₂ - y₁))) := by
    match_scalars <;> field_simp <;> ring
  rw [heq]
  exact hΩ hs hb (sub_nonneg.2 hμ1) hμ.le (by ring)

/-- **The ray length varies in a Lipschitz way near `a`**: for `Ω` convex with `‖x‖ ≤ C` on `Ω` and
`B(a, δ) ⊆ Ω`, `‖ν‖ = 1` and `‖y₁‖, ‖y₂‖ < δ/4`,
`ℓ(y₁) ≤ ℓ(y₂) + (4C/δ) ‖y₁ - y₂‖`. Every admissible `s` for `y₁` gives the admissible `(1 - μ) s`
for `y₂` (`Rd.sub_smul_mem_of_norm_lt`), and `μ s ≤ 2μC = (4C/δ) ‖y₁ - y₂‖`
(`Rd.rayLength_le`). -/
theorem rayLength_le_rayLength_add (hΩ : Convex ℝ Ω) (hC : ∀ x ∈ Ω, ‖x‖ ≤ C) (hν : ‖ν‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) (hball : ball a δ ⊆ Ω) {y₁ y₂ : V} (h₁ : ‖y₁‖ < δ / 4)
    (h₂ : ‖y₂‖ < δ / 4) :
    rayLength Ω a ν y₁ ≤ rayLength Ω a ν y₂ + 4 * C / δ * ‖y₁ - y₂‖ := by
  have hy₁ : a + y₁ ∈ Ω := hball (add_mem_ball_iff_norm.2 (by linarith))
  refine csSup_le (nonempty_raySet hy₁) fun s hs => ?_
  have h1 := le_rayLength hC hν (sub_smul_mem_of_norm_lt hΩ hδ hball h₁ h₂ hs)
  have h2 : s ≤ 2 * C := (le_rayLength hC hν hs).trans (rayLength_le hC hν hy₁)
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * ‖y₁ - y₂‖ / δ)
  have h4 : 2 * ‖y₁ - y₂‖ / δ * (2 * C) = 4 * C / δ * ‖y₁ - y₂‖ := by ring
  linarith

omit [InnerProductSpace ℝ V] in
/-- The constant `4C/δ` of the cone estimate is nonnegative when `a ∈ Ω`, `‖x‖ ≤ C` on `Ω` and
`δ ≥ 0`. -/
theorem cone_const_nonneg (hC : ∀ x ∈ Ω, ‖x‖ ≤ C) (ha : a ∈ Ω) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ 4 * C / δ :=
  div_nonneg (mul_nonneg zero_le_four ((norm_nonneg a).trans (hC a ha))) hδ

/-- **The ray length is `4C/δ`-Lipschitz on the ball `B(0, δ/4)`**, for `Ω` convex with
`‖x‖ ≤ C` on `Ω`, `B(a, δ) ⊆ Ω` and `‖ν‖ = 1` (`Rd.rayLength_le_rayLength_add`). -/
theorem lipschitzOnWith_rayLength (hΩ : Convex ℝ Ω) (hC : ∀ x ∈ Ω, ‖x‖ ≤ C) (hν : ‖ν‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) (hball : ball a δ ⊆ Ω) :
    LipschitzOnWith (4 * C / δ).toNNReal (rayLength Ω a ν) (ball 0 (δ / 4)) :=
  LipschitzOnWith.of_le_add_mul _ fun y₁ h₁ y₂ h₂ => by
    rw [Real.coe_toNNReal _ (cone_const_nonneg hC (hball (mem_ball_self hδ)) hδ.le),
      dist_eq_norm]
    exact rayLength_le_rayLength_add hΩ hC hν hδ hball (mem_ball_zero_iff.1 h₁)
      (mem_ball_zero_iff.1 h₂)

/-- **The graph function of a convex set**: for `Ω` convex with `‖x‖ ≤ C` on `Ω`, `B(a, δ) ⊆ Ω`,
`δ > 0` and `‖ν‖ = 1`, and for every `d ∈ ℝ`, the function `y ↦ d - ℓ(y)` on the hyperplane `ν^⊥`
is `4C/δ`-Lipschitz on the ball `B(0, δ/4)` of `ν^⊥` (`Rd.rayLength_le_rayLength_add` with the
roles of `y₁` and `y₂` exchanged). -/
theorem lipschitzOnWith_sub_rayLength (hΩ : Convex ℝ Ω) (hC : ∀ x ∈ Ω, ‖x‖ ≤ C) (hν : ‖ν‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) (hball : ball a δ ⊆ Ω) (d : ℝ) :
    LipschitzOnWith (4 * C / δ).toNNReal (fun y : (ℝ ∙ ν)ᗮ => d - rayLength Ω a ν y)
      (ball 0 (δ / 4)) :=
  LipschitzOnWith.of_le_add_mul _ fun y₁ h₁ y₂ h₂ => by
    rw [Real.coe_toNNReal _ (cone_const_nonneg hC (hball (mem_ball_self hδ)) hδ.le),
      dist_comm, Subtype.dist_eq, dist_eq_norm]
    have h := rayLength_le_rayLength_add hΩ hC hν hδ hball (mem_ball_zero_iff.1 h₂)
      (mem_ball_zero_iff.1 h₁)
    linarith

/-! ### Convex sets near a frontier point -/

/-- **A convex set near a frontier point is the region above a graph**: let `Ω` be convex, open,
with `‖x‖ ≤ C` on `Ω` and `B(a, δ) ⊆ Ω`, let `‖ν‖ = 1`, `a - z = d ν` with `δ ≤ d`, and
`‖x - z‖ < δ/4`. Then `x ∈ Ω` iff `d - ℓ(P(x - z)) < ⟪ν, x - z⟫`, `P` the orthogonal projection
onto `ν^⊥`. Indeed `x = a + P(x - z) - (d - ⟪ν, x - z⟫) ν`
(`Rd.coe_orthogonalProjectionOnto_orthogonalComplement_singleton`), `a + P(x - z) ∈ B(a, δ)`,
`d - ⟪ν, x - z⟫ ≥ 0`, and `Rd.mem_iff_lt_rayLength` applies. -/
theorem mem_iff_sub_rayLength_lt (hΩ : Convex ℝ Ω) (ho : IsOpen Ω) (hC : ∀ x ∈ Ω, ‖x‖ ≤ C)
    {δ : ℝ} (hball : ball a δ ⊆ Ω) {z : V} {d : ℝ} (hν : ‖ν‖ = 1) (hd : a - z = d • ν)
    (hδd : δ ≤ d) {x : V} (hx : ‖x - z‖ < δ / 4) :
    x ∈ Ω ↔ d - rayLength Ω a ν ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z) : V) <
      inner ℝ ν (x - z) := by
  have hP := coe_orthogonalProjectionOnto_orthogonalComplement_singleton hν (x - z)
  have hPn : ‖((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z) : V)‖ < δ / 4 :=
    (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans_lt hx
  have hy : a + ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z) : V) ∈ Ω :=
    hball (add_mem_ball_iff_norm.2 (by linarith [norm_nonneg (x - z)]))
  have ht : inner ℝ ν (x - z) ≤ ‖x - z‖ := by
    simpa only [hν, one_mul] using real_inner_le_norm ν (x - z)
  have hx' : x = a + ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z) : V) -
      (d - inner ℝ ν (x - z)) • ν := by
    rw [hP, show a = z + d • ν by rw [← hd]; abel]
    module
  rw [sub_lt_comm]
  conv_lhs => rw [hx']
  exact mem_iff_lt_rayLength hΩ ho hC hν hy (by linarith [norm_nonneg (x - z)])

/-- **A bounded open convex set is Lipschitz near each frontier point**: pick `a ∈ Ω` with
`B(a, δ) ⊆ Ω` (the frontier point `z` lies in the closure, so `Ω` is nonempty); then
`d = ‖a - z‖ ≥ δ` since `z ∉ Ω`, and with `ν = (a - z)/d`, radius `δ/4` and the graph function
`y ↦ d - ℓ(y)` (`Rd.mem_iff_sub_rayLength_lt`, `Rd.lipschitzOnWith_sub_rayLength`), McShane's
extension (`Rd.isLipschitzDomainAt_of_lipschitzOnWith`) gives the local condition. -/
theorem isLipschitzDomainAt_of_convex (hΩ : Convex ℝ Ω) (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {z : V} (hz : z ∈ frontier Ω) : IsLipschitzDomainAt Ω z := by
  obtain ⟨a, ha⟩ : Ω.Nonempty := closure_nonempty_iff.1 ⟨z, frontier_subset_closure hz⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 ho a ha
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  have hzΩ : z ∉ Ω := ((ho.frontier_eq ▸ hz) : z ∈ closure Ω \ Ω).2
  have hδd : δ ≤ ‖a - z‖ := by
    by_contra h
    exact hzΩ (hball (by rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith))
  have hd : 0 < ‖a - z‖ := hδ.trans_le hδd
  have hν : ‖‖a - z‖⁻¹ • (a - z)‖ = 1 := by
    simpa using norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.1 hd)
  have had : a - z = ‖a - z‖ • (‖a - z‖⁻¹ • (a - z)) := (smul_inv_smul₀ hd.ne' (a - z)).symm
  refine isLipschitzDomainAt_of_lipschitzOnWith (by positivity) hν
    (lipschitzOnWith_sub_rayLength hΩ hC hν hδ hball ‖a - z‖) ?_
  ext x
  refine ⟨fun ⟨hx, hxb⟩ => ⟨?_, hxb⟩, fun ⟨hx, hxb⟩ => ⟨?_, hxb⟩⟩
  · exact (mem_iff_sub_rayLength_lt hΩ ho hC hball hν had hδd (mem_ball_iff_norm.1 hxb)).1 hx
  · exact (mem_iff_sub_rayLength_lt hΩ ho hC hball hν had hδd (mem_ball_iff_norm.1 hxb)).2 hx

/-- **Every open convex set is Lipschitz near each frontier point**, bounded or not: near `z` the
set `Ω` agrees with the bounded open convex set `Ω ∩ B(z, 1)`, which has `z` on its frontier
(Mathlib's `IsOpen.closure_inter`), so `Rd.isLipschitzDomainAt_of_convex` and
`Rd.IsLipschitzDomainAt.congr_ball` apply. Half-spaces and epigraphs of convex functions are
examples. -/
theorem isLipschitzDomainAt_of_convex_of_isOpen (hΩ : Convex ℝ Ω) (ho : IsOpen Ω) {z : V}
    (hz : z ∈ frontier Ω) : IsLipschitzDomainAt Ω z := by
  have hzΩ : z ∉ Ω := ((ho.frontier_eq ▸ hz) : z ∈ closure Ω \ Ω).2
  have hz' : z ∈ frontier (Ω ∩ ball z 1) := by
    rw [(ho.inter isOpen_ball).frontier_eq]
    exact ⟨isOpen_ball.closure_inter ⟨frontier_subset_closure hz, mem_ball_self one_pos⟩,
      fun h => hzΩ h.1⟩
  refine IsLipschitzDomainAt.congr_ball one_pos ?_
    (isLipschitzDomainAt_of_convex (hΩ.inter (convex_ball z 1)) (ho.inter isOpen_ball)
      (isBounded_ball.subset inter_subset_right) hz')
  rw [inter_comm Ω, ← inter_assoc, inter_self]

/-- **Every bounded open convex set is a bounded Lipschitz set**
(`Rd.isLipschitzDomainAt_of_convex` at each frontier point). -/
theorem isBoundedLipschitzDomain_of_convex (hΩ : Convex ℝ Ω) (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) : IsBoundedLipschitzDomain Ω :=
  ⟨ho, hb, fun _ hz => isLipschitzDomainAt_of_convex hΩ ho hb hz⟩

/-- **A bounded open convex set as a bounded Lipschitz domain**, in finite dimension
(`Rd.isBoundedLipschitzDomain_of_convex` and
`Rd.BoundedLipschitzDomain.ofIsBoundedLipschitzDomain`). -/
noncomputable def BoundedLipschitzDomain.ofConvex [FiniteDimensional ℝ V] (hΩ : Convex ℝ Ω)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) : BoundedLipschitzDomain V :=
  BoundedLipschitzDomain.ofIsBoundedLipschitzDomain (isBoundedLipschitzDomain_of_convex hΩ ho hb)

/-- The carrier of `Rd.BoundedLipschitzDomain.ofConvex hΩ ho hb` is `Ω`. -/
@[simp]
theorem BoundedLipschitzDomain.carrier_ofConvex [FiniteDimensional ℝ V] (hΩ : Convex ℝ Ω)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (BoundedLipschitzDomain.ofConvex hΩ ho hb).carrier = Ω :=
  rfl

/-! ### The open unit cube -/

/-- **The open unit cube is convex**: `(0, 1)^n ⊆ ℝ^n` is convex coordinatewise
(Mathlib's `convex_Ioo`). -/
theorem convex_unitCube (n : ℕ) :
    Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1} := by
  intro x hx y hy s t hs ht hst i
  simp only [PiLp.add_apply, PiLp.smul_apply]
  exact convex_Ioo (0 : ℝ) 1 (hx i) (hy i) hs ht hst

/-- **The open unit cube is nonempty**: it contains the centre `(1/2, …, 1/2)`. -/
theorem nonempty_unitCube (n : ℕ) :
    {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1}.Nonempty :=
  ⟨WithLp.toLp 2 fun _ => 1 / 2, fun _ => show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num⟩

/-- The closed unit cube `[0, 1]^n ⊆ ℝ^n` is the preimage of the product `∏_i [0, 1]` under
Mathlib's homeomorphism `PiLp.homeomorph` between `ℝ^n` and the product space. -/
theorem closedUnitCube_eq_preimage (n : ℕ) :
    {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Icc (0 : ℝ) 1} =
      PiLp.homeomorph 2 _ ⁻¹' univ.pi (fun _ => Icc (0 : ℝ) 1) := by
  ext
  simp [PiLp.homeomorph, -pi_univ_Icc]

/-- The open unit cube `(0, 1)^n ⊆ ℝ^n` is the preimage of the product `∏_i (0, 1)` under
Mathlib's homeomorphism `PiLp.homeomorph` between `ℝ^n` and the product space. -/
theorem unitCube_eq_preimage (n : ℕ) :
    {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1} =
      PiLp.homeomorph 2 _ ⁻¹' univ.pi (fun _ => Ioo (0 : ℝ) 1) := by
  ext
  simp [PiLp.homeomorph]

/-- **The closed unit cube is closed**: `[0, 1]^n ⊆ ℝ^n` is the preimage of a product of closed
intervals under a homeomorphism (`Rd.closedUnitCube_eq_preimage`, Mathlib's `isClosed_set_pi`). -/
theorem isClosed_closedUnitCube (n : ℕ) :
    IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
  rw [closedUnitCube_eq_preimage]
  exact (isClosed_set_pi fun _ _ => isClosed_Icc).preimage (PiLp.homeomorph 2 _).continuous

/-- **The closure of the open unit cube is the closed unit cube**: closures commute with
homeomorphisms and with products (`Rd.unitCube_eq_preimage`, Mathlib's
`Homeomorph.preimage_closure`, `closure_pi_set`), and the closure of `(0, 1)` is `[0, 1]`
(Mathlib's `closure_Ioo`). -/
theorem closure_unitCube (n : ℕ) :
    closure {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1} =
      {x | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
  rw [unitCube_eq_preimage, ← Homeomorph.preimage_closure, closure_pi_set,
    closure_Ioo zero_ne_one, closedUnitCube_eq_preimage]

/-- **The open unit cube is a bounded Lipschitz set**: `(0, 1)^n ⊆ ℝ^n` is convex
(`Rd.convex_unitCube`), open (an intersection of finitely many open slabs) and bounded
(`‖x‖ ≤ √n` on it, `EuclideanSpace.norm_eq`), so `Rd.isBoundedLipschitzDomain_of_convex`
applies. -/
theorem isBoundedLipschitzDomain_unitCube (n : ℕ) :
    IsBoundedLipschitzDomain {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1} := by
  refine isBoundedLipschitzDomain_of_convex (convex_unitCube n) ?_ ?_
  · have h : {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1} =
        ⋂ i, (fun x : EuclideanSpace ℝ (Fin n) => x i) ⁻¹' Ioo 0 1 := by
      ext x
      simp
    rw [h]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (by fun_prop)
  · refine isBounded_iff_forall_norm_le.2 ⟨Real.sqrt n, fun x hx => ?_⟩
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs, sq_abs]
          exact pow_le_one₀ (hx i).1.le (hx i).2.le
      _ = n := by simp

/-- **The open unit cube as a bounded Lipschitz domain** in `ℝ^n`
(`Rd.isBoundedLipschitzDomain_unitCube`). -/
protected noncomputable def BoundedLipschitzDomain.unitCube (n : ℕ) :
    BoundedLipschitzDomain (EuclideanSpace ℝ (Fin n)) :=
  BoundedLipschitzDomain.ofIsBoundedLipschitzDomain (isBoundedLipschitzDomain_unitCube n)

/-- The carrier of `Rd.BoundedLipschitzDomain.unitCube n` is the open unit cube `(0, 1)^n`. -/
@[simp]
theorem BoundedLipschitzDomain.carrier_unitCube (n : ℕ) :
    (BoundedLipschitzDomain.unitCube n).carrier =
      {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1} :=
  rfl

end Rd
