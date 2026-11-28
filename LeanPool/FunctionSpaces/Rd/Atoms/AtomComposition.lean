/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Atoms.SmoothAtoms

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smooth atoms under smooth changes of variables

Let `Ω` be a closed convex set with nonempty interior, the model being the closed half-space. A
**smooth change of variables with a cut-off** on `Ω` (`Rd.CutoffDiffeo`) consists of a map `Φ`
from a relatively open part `Ω ∩ U` onto another one `Ω ∩ U'`, smooth within `Ω` with smooth
inverse `Ψ`, and a function `χ` that is smooth within `Ω ∩ U'` and vanishes on `Ω` outside a
compact set `K₀ ⊆ Ω ∩ U'`. It acts on functions by

`T f = 1_{Ω ∩ U} (χ f) ∘ Φ`   (`Rd.CutoffDiffeo.apply`).

The pieces of a function on a manifold in two overlapping charts are related in this way; on
`Ω = V`, `χ` a smooth cut-off and `Φ = id` it is a pointwise multiplier. `T f` vanishes outside
the compact set `Ψ(K₀)` and is continuous on `Ω` for continuous `f`
(`Rd.CutoffDiffeo.continuousOn_apply`).

**Smooth atoms stay smooth atoms** (`Rd.CutoffDiffeo.isSmoothAtom_apply`): there are `L` and `A'`,
depending only on `T` and the order `K`, such that for a smooth atom `a` on `V` of level `j`,
radius factor `d` and constant `A`, and a point `y₀ ∈ K₀` within `d 2^(-j)` of its centre,
`T a` is a smooth atom on `Ω` with centre `Ψ y₀`, radius factor `2 L d` and constant `A' A`.
Only `Ψ(K₀)` carries `T a`; there the derivatives of `Φ` are bounded, `Ψ` is Lipschitz on `K₀`
(`Rd.exists_lipschitzOnWith_of_contDiffOn_inter`), and Leibniz's rule and the chain rule within
sets (Mathlib's `norm_iteratedFDerivWithin_mul_le`, `norm_iteratedFDerivWithin_comp_le`) give
`‖D^l (T a)‖ ≤ l! 2^l M_χ A D^l 2^(jl)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal NNReal

namespace Rd

/-! ### Calculus within a relatively open part of a convex set -/

section Within

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A map of class `C^1` within a relatively open part `Ω ∩ U` of a convex set `Ω` is locally
Lipschitz there. -/
theorem locallyLipschitzOn_inter {Ω U : Set E} (hΩ : Convex ℝ Ω) (hU : IsOpen U) {f : E → F}
    {n : WithTop ℕ∞} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f (Ω ∩ U)) :
    LocallyLipschitzOn (Ω ∩ U) f := by
  intro x hx
  have h1 : ContDiffWithinAt ℝ 1 f Ω x :=
    (contDiffWithinAt_inter (hU.mem_nhds hx.2)).1 ((hf x hx).of_le hn)
  obtain ⟨K, t, ht, hL⟩ := h1.exists_lipschitzOnWith hΩ
  exact ⟨K, t, nhdsWithin_mono x inter_subset_left ht, hL⟩

/-- A map of class `C^1` within a relatively open part of a convex set is Lipschitz on its compact
subsets. -/
theorem exists_lipschitzOnWith_of_contDiffOn_inter {Ω U : Set E} (hΩ : Convex ℝ Ω)
    (hU : IsOpen U) {f : E → F} {n : WithTop ℕ∞} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f (Ω ∩ U))
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ Ω ∩ U) : ∃ L, LipschitzOnWith L f K :=
  ((locallyLipschitzOn_inter hΩ hU hn hf).mono hKs).exists_lipschitzOnWith_of_compact hK

/-- **Derivatives of a function that vanishes near a point**: if `f = 0` on `s ∩ u` for an open
`u ∋ x`, then the derivatives of `f` within `s` vanish at `x ∈ s`. -/
theorem iteratedFDerivWithin_eq_zero_of_eqOn {s u : Set E} (hu : IsOpen u) {x : E} (hxu : x ∈ u)
    (hxs : x ∈ s) {f : E → F} (hf : ∀ y ∈ s ∩ u, f y = 0) (n : ℕ) :
    iteratedFDerivWithin ℝ n f s x = 0 := by
  have h : f =ᶠ[𝓝[s] x] fun _ => 0 :=
    mem_nhdsWithin.2 ⟨u, hu, hxu, fun y hy => hf y ⟨hy.2, hy.1⟩⟩
  rw [h.iteratedFDerivWithin_eq (hf x ⟨hxs, hxu⟩) n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext; simp
  · exact congrFun (iteratedFDerivWithin_const_of_ne (𝕜 := ℝ) hn.ne' (0 : F) s) x

end Within

/-! ### Smooth changes of variables with a cut-off -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A **smooth change of variables with a cut-off** on `Ω`: a bijection `Φ : Ω ∩ U → Ω ∩ U'`,
smooth within `Ω` with smooth inverse `Ψ`, and a function `χ` that is smooth within `Ω ∩ U'` and
vanishes on `Ω` outside a compact set `K₀ ⊆ Ω ∩ U'`. -/
structure CutoffDiffeo (Ω : Set V) where
  /-- The open set cutting out the source. -/
  U : Set V
  /-- The open set cutting out the target. -/
  U' : Set V
  isOpen_U : IsOpen U
  isOpen_U' : IsOpen U'
  /-- The change of variables. -/
  Phi : V → V
  /-- Its inverse. -/
  Psi : V → V
  /-- The cut-off. -/
  chi : V → ℂ
  /-- The compact set carrying the cut-off. -/
  K0 : Set V
  contDiffOn_Phi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi (Ω ∩ U)
  contDiffOn_Psi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi (Ω ∩ U')
  contDiffOn_chi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi (Ω ∩ U')
  mapsTo_Phi : MapsTo Phi (Ω ∩ U) (Ω ∩ U')
  mapsTo_Psi : MapsTo Psi (Ω ∩ U') (Ω ∩ U)
  left_inv : ∀ x ∈ Ω ∩ U, Psi (Phi x) = x
  right_inv : ∀ y ∈ Ω ∩ U', Phi (Psi y) = y
  isCompact_K0 : IsCompact K0
  K0_subset : K0 ⊆ Ω ∩ U'
  chi_eq_zero : ∀ y ∈ Ω, y ∉ K0 → chi y = 0

namespace CutoffDiffeo

variable {Ω : Set V} (T : CutoffDiffeo Ω)

/-- The action on functions: `T f = 1_{Ω ∩ U} (χ f) ∘ Φ`. -/
noncomputable def apply (f : V → ℂ) : V → ℂ :=
  (Ω ∩ T.U).indicator fun x => T.chi (T.Phi x) * f (T.Phi x)

/-- The compact set `Ψ(K₀)` that carries the images. -/
def carrier : Set V := T.Psi '' T.K0

/-- `Ψ(K₀)` is compact. -/
theorem isCompact_carrier : IsCompact T.carrier :=
  T.isCompact_K0.image_of_continuousOn (T.contDiffOn_Psi.continuousOn.mono T.K0_subset)

/-- `Ψ(K₀) ⊆ Ω ∩ U`. -/
theorem carrier_subset : T.carrier ⊆ Ω ∩ T.U := by
  rintro _ ⟨y, hy, rfl⟩
  exact T.mapsTo_Psi (T.K0_subset hy)

/-- **`T f` vanishes on `Ω` outside `Ψ(K₀)`**: if `Φ x ∉ K₀`, the cut-off vanishes. -/
theorem apply_eq_zero_of_notMem (f : V → ℂ) {x : V} (hx : x ∉ T.carrier) : T.apply f x = 0 := by
  by_cases hxs : x ∈ Ω ∩ T.U
  · rw [apply, Set.indicator_of_mem hxs]
    have hΦ : T.Phi x ∉ T.K0 := fun h => hx ⟨T.Phi x, h, T.left_inv x hxs⟩
    rw [T.chi_eq_zero _ (T.mapsTo_Phi hxs).1 hΦ, zero_mul]
  · rw [apply, Set.indicator_of_notMem hxs]

/-- **`T` keeps continuity on `Ω`**: for continuous `f`, `T f` is continuous on `Ω`. Near a point
of `Ψ(K₀)` it is `(χ f) ∘ Φ`, and off the compact set `Ψ(K₀)` it vanishes. -/
theorem continuousOn_apply {f : V → ℂ} (hf : Continuous f) : ContinuousOn (T.apply f) Ω := by
  intro x hx
  by_cases hxK : x ∈ T.carrier
  · have hxU : x ∈ T.U := (T.carrier_subset hxK).2
    have hcont : ContinuousOn (fun y => T.chi (T.Phi y) * f (T.Phi y)) (Ω ∩ T.U) :=
      (T.contDiffOn_chi.continuousOn.comp T.contDiffOn_Phi.continuousOn T.mapsTo_Phi).mul
        (hf.comp_continuousOn T.contDiffOn_Phi.continuousOn)
    have hwithin := (continuousWithinAt_inter (T.isOpen_U.mem_nhds hxU)).1 (hcont x ⟨hx, hxU⟩)
    refine hwithin.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (T.isOpen_U.mem_nhds hxU),
        self_mem_nhdsWithin] with y hyU hyΩ
      rw [apply, Set.indicator_of_mem (Set.mem_inter hyΩ hyU)]
    · rw [apply, Set.indicator_of_mem (Set.mem_inter hx hxU)]
  · have hev : T.apply f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [T.isCompact_carrier.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact T.apply_eq_zero_of_notMem f hy
    exact (continuousAt_const.congr hev.symm).continuousWithinAt

/-- **`T a` vanishes if `a` lives far from `K₀`**: if `a = 0` outside `B(c, d 2^(-j))` and no
point of `K₀` lies in that ball, then `T a = 0`. -/
theorem apply_eq_zero_of_forall_far {d : ℝ} {j : ℕ} {c : V} {a : V → ℂ}
    (ha : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0) (hfar : ∀ y ∈ T.K0, d / 2 ^ j < ‖y - c‖) (x : V) :
    T.apply a x = 0 := by
  by_cases hxs : x ∈ Ω ∩ T.U
  · rw [apply, Set.indicator_of_mem hxs]
    by_cases hΦ : T.Phi x ∈ T.K0
    · rw [ha _ (hfar _ hΦ), mul_zero]
    · rw [T.chi_eq_zero _ (T.mapsTo_Phi hxs).1 hΦ, zero_mul]
  · rw [apply, Set.indicator_of_notMem hxs]

variable (hΩ : Convex ℝ Ω) (hint : (interior Ω).Nonempty)
include hΩ hint

/-- Unique differentiability on the source. -/
theorem uniqueDiffOn_source : UniqueDiffOn ℝ (Ω ∩ T.U) :=
  (uniqueDiffOn_convex hΩ hint).inter T.isOpen_U

/-- Unique differentiability on the target. -/
theorem uniqueDiffOn_target : UniqueDiffOn ℝ (Ω ∩ T.U') :=
  (uniqueDiffOn_convex hΩ hint).inter T.isOpen_U'

omit hint in
/-- `Ψ` is Lipschitz on `K₀`. -/
theorem exists_lipschitzOnWith_Psi : ∃ L : ℝ≥0, LipschitzOnWith L T.Psi T.K0 :=
  exists_lipschitzOnWith_of_contDiffOn_inter hΩ T.isOpen_U' (by exact_mod_cast le_top)
    T.contDiffOn_Psi T.isCompact_K0 T.K0_subset

omit hint in
/-- `Φ` is Lipschitz on `Ψ(K₀)`. -/
theorem exists_lipschitzOnWith_Phi : ∃ L : ℝ≥0, LipschitzOnWith L T.Phi T.carrier :=
  exists_lipschitzOnWith_of_contDiffOn_inter hΩ T.isOpen_U (by exact_mod_cast le_top)
    T.contDiffOn_Phi T.isCompact_carrier T.carrier_subset

/-- **The derivatives of the cut-off are bounded**: `‖D^l χ‖ ≤ M` within `Ω ∩ U'` for `l ≤ K`;
on the compact `K₀` by continuity (`ContDiffOn.exists_norm_iteratedFDerivWithin_le`), elsewhere
they vanish. -/
theorem exists_iteratedFDerivWithin_chi_bound (K : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l ≤ K, ∀ y ∈ Ω ∩ T.U', ‖iteratedFDerivWithin ℝ l T.chi (Ω ∩ T.U') y‖ ≤ M
      := by
  obtain ⟨C, hC⟩ := T.contDiffOn_chi.exists_norm_iteratedFDerivWithin_le
    (T.uniqueDiffOn_target hΩ hint) T.isCompact_K0 T.K0_subset K
  refine ⟨max C 0, le_max_right _ _, fun l hl y hy => ?_⟩
  by_cases hyK : y ∈ T.K0
  · exact (hC l hl y hyK).trans (le_max_left _ _)
  · have hzero : iteratedFDerivWithin ℝ l T.chi (Ω ∩ T.U') y = 0 :=
      iteratedFDerivWithin_eq_zero_of_eqOn T.isCompact_K0.isClosed.isOpen_compl hyK hy
        (fun z hz => T.chi_eq_zero z hz.1.1 hz.2) l
    rw [hzero, norm_zero]
    exact le_max_right _ _

/-- **The derivatives of `Φ` are bounded on `Ψ(K₀)`**: `‖D^i Φ‖ ≤ D` within `Ω ∩ U` for
`i ≤ K`, with `D ≥ 1` (`ContDiffOn.exists_norm_iteratedFDerivWithin_le`). -/
theorem exists_iteratedFDerivWithin_Phi_bound (K : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ K, ∀ x ∈ T.carrier,
      ‖iteratedFDerivWithin ℝ i T.Phi (Ω ∩ T.U) x‖ ≤ D := by
  obtain ⟨C, hC⟩ := T.contDiffOn_Phi.exists_norm_iteratedFDerivWithin_le
    (T.uniqueDiffOn_source hΩ hint) T.isCompact_carrier T.carrier_subset K
  exact ⟨max 1 C, le_max_left _ _, fun i hi x hx => (hC i hi x hx).trans (le_max_right _ _)⟩

end CutoffDiffeo

/-! ### Smooth atoms under the change of variables -/

section Atoms

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Bounded overlap of transported centres**: let `Φ` be `L`-Lipschitz on `B`, and let the
points `z_m ∈ B` satisfy `‖Φ z_m - c_{j,m}‖ ≤ d 2^(-j)` for the centres `c_{j,m}` of the cells of
level `j`. Then at most `⌈(2 (2 L ρ + d) + 2)^n⌉` of the `z_m` lie in a ball of radius
`ρ 2^(-j)`. -/
theorem card_le_of_lipschitz_centres {B : Set V} {Phi : V → V} {L : ℝ≥0}
    (hΦ : LipschitzOnWith L Phi B) (j : ℕ) {d ρ : ℝ} (hd : 0 ≤ d) (hρ : 0 ≤ ρ)
    {z : (Fin (finrank ℝ V) → ℤ) → V} (x : V) (S : Finset (Fin (finrank ℝ V) → ℤ))
    (hS : ∀ m ∈ S, z m ∈ B ∧ ‖Phi (z m) - cellCenter j m‖ ≤ d / 2 ^ j ∧ ‖x - z m‖ ≤ ρ / 2 ^ j) :
    S.card ≤ ⌈(2 * (2 * L * ρ + d) + 2) ^ finrank ℝ V⌉₊ := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨m₀, hm₀⟩
  · simp [hS0]
  refine card_le_of_norm_sub_cellCenter_le j (by positivity) (Phi (z m₀)) S fun m hm => ?_
  obtain ⟨hz0, -, hx0⟩ := hS m₀ hm₀
  obtain ⟨hz, hc, hx⟩ := hS m hm
  have h1 : ‖Phi (z m₀) - Phi (z m)‖ ≤ L * (2 * ρ / 2 ^ j) := by
    have := hΦ.dist_le_mul (z m₀) hz0 (z m) hz
    rw [dist_eq_norm, dist_eq_norm] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    calc ‖z m₀ - z m‖ = ‖(x - z m) - (x - z m₀)‖ := by congr 1; abel
      _ ≤ ‖x - z m‖ + ‖x - z m₀‖ := norm_sub_le _ _
      _ ≤ ρ / 2 ^ j + ρ / 2 ^ j := add_le_add hx hx0
      _ = 2 * ρ / 2 ^ j := by ring
  calc ‖Phi (z m₀) - cellCenter j m‖ = ‖(Phi (z m₀) - Phi (z m)) + (Phi (z m) - cellCenter j m)‖
    := by
        congr 1; abel
    _ ≤ ‖Phi (z m₀) - Phi (z m)‖ + ‖Phi (z m) - cellCenter j m‖ := norm_add_le _ _
    _ ≤ L * (2 * ρ / 2 ^ j) + d / 2 ^ j := add_le_add h1 hc
    _ = (2 * L * ρ + d) / 2 ^ j := by ring

namespace CutoffDiffeo

variable {Ω : Set V} (T : CutoffDiffeo Ω)

/-- **Derivatives of `χ a`**: for a smooth atom `a` on `V` with constant `A` and `‖D^k χ‖ ≤ M`
within `Ω ∩ U'`, `‖D^i (χ a)‖ ≤ 2^i M A 2^(ji)` within `Ω ∩ U'` for `i ≤ K`. -/
theorem norm_iteratedFDerivWithin_mul_atom_le (hΩ : Convex ℝ Ω) (hint : (interior Ω).Nonempty)
    {K : ℕ} {M : ℝ} (hM : ∀ l ≤ K, ∀ y ∈ Ω ∩ T.U', ‖iteratedFDerivWithin ℝ l T.chi (Ω ∩ T.U') y‖
      ≤ M)
    {d A : ℝ} (hA : 0 ≤ A) {j : ℕ} {c : V} {a : V → ℂ} (ha : IsSmoothAtom Set.univ K d A j c a)
    {i : ℕ} (hi : i ≤ K) {y : V} (hy : y ∈ Ω ∩ T.U') :
    ‖iteratedFDerivWithin ℝ i (fun z => T.chi z * a z) (Ω ∩ T.U') y‖ ≤
      2 ^ i * M * A * 2 ^ (j * i) := by
  have ht := T.uniqueDiffOn_target hΩ hint
  have hac : ContDiff ℝ K a := contDiffOn_univ.1 ha.contDiffOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le K) y hy)
  have ha' : ∀ k ≤ K, ‖iteratedFDerivWithin ℝ k a (Ω ∩ T.U') y‖ ≤ A * 2 ^ (j * k) :=
    fun k hk => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv ht (hac.contDiffAt.of_le (by exact_mod_cast hk))
        hy, ← iteratedFDerivWithin_univ]
      exact ha.norm_iteratedFDerivWithin_le k hk y (Set.mem_univ y)
  refine (norm_iteratedFDerivWithin_mul_le (T.contDiffOn_chi.of_le (by exact_mod_cast le_top))
    hac.contDiffOn ht hy (by exact_mod_cast hi)).trans ?_
  calc ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        ‖iteratedFDerivWithin ℝ k T.chi (Ω ∩ T.U') y‖ *
          ‖iteratedFDerivWithin ℝ (i - k) a (Ω ∩ T.U') y‖
      ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * (M * A * 2 ^ (j * i)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hki : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc ‖iteratedFDerivWithin ℝ k T.chi (Ω ∩ T.U') y‖ *
              ‖iteratedFDerivWithin ℝ (i - k) a (Ω ∩ T.U') y‖
            ≤ M * (A * 2 ^ (j * (i - k))) :=
              mul_le_mul (hM k (hki.trans hi) y hy) (ha' (i - k) ((Nat.sub_le i k).trans hi))
                (norm_nonneg _) hM0
          _ ≤ M * (A * 2 ^ (j * i)) := by
              gcongr
              · exact one_le_two
              · exact Nat.sub_le i k
          _ = M * A * 2 ^ (j * i) := by ring
    _ = 2 ^ i * M * A * 2 ^ (j * i) := by
        rw [← Finset.sum_mul]
        have hsum : ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) = 2 ^ i := by
          exact_mod_cast Nat.sum_range_choose i
        rw [hsum]
        ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The changed atom vanishes far from `Ψ(y₀)`**: if `a` vanishes outside `B(c, d 2^(-j))`,
`y₀ ∈ K₀` lies within `d 2^(-j)` of `c` and `Ψ` is `L`-Lipschitz on `K₀`, then `T a` vanishes
outside `B(Ψ y₀, 2 L d 2^(-j))`. -/
theorem apply_eq_zero_of_far {L : ℝ≥0} (hL : LipschitzOnWith L T.Psi T.K0) {d : ℝ} {j : ℕ} {c : V}
    {a : V → ℂ} (ha : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0) {y₀ : V} (hy₀ : y₀ ∈ T.K0)
    (hy₀c : ‖y₀ - c‖ ≤ d / 2 ^ j) {x : V} (hx : 2 * L * d / 2 ^ j < ‖x - T.Psi y₀‖) :
    T.apply a x = 0 := by
  by_contra hb
  have hxs : x ∈ Ω ∩ T.U := by
    by_contra hxs
    exact hb (by rw [apply, Set.indicator_of_notMem hxs])
  rw [apply, Set.indicator_of_mem hxs] at hb
  have hΦK : T.Phi x ∈ T.K0 := by
    by_contra hΦK
    exact hb (by rw [T.chi_eq_zero _ (T.mapsTo_Phi hxs).1 hΦK, zero_mul])
  have hΦc : ‖T.Phi x - c‖ ≤ d / 2 ^ j := not_lt.1 fun h => hb (by rw [ha _ h, mul_zero])
  have h1 : ‖x - T.Psi y₀‖ ≤ L * ‖T.Phi x - y₀‖ := by
    have := hL.dist_le_mul (T.Phi x) hΦK y₀ hy₀
    rwa [T.left_inv x hxs, dist_eq_norm, dist_eq_norm] at this
  have h2 : ‖T.Phi x - y₀‖ ≤ 2 * d / 2 ^ j := by
    calc ‖T.Phi x - y₀‖ = ‖(T.Phi x - c) - (y₀ - c)‖ := by congr 1; abel
      _ ≤ ‖T.Phi x - c‖ + ‖y₀ - c‖ := norm_sub_le _ _
      _ ≤ d / 2 ^ j + d / 2 ^ j := add_le_add hΦc hy₀c
      _ = 2 * d / 2 ^ j := by ring
  have h3 : ‖x - T.Psi y₀‖ ≤ 2 * L * d / 2 ^ j := by
    calc ‖x - T.Psi y₀‖ ≤ L * (2 * d / 2 ^ j) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 L.coe_nonneg)
      _ = 2 * L * d / 2 ^ j := by ring
  exact absurd hx (not_lt.2 h3)

/-- **Smooth atoms stay smooth atoms** under a smooth change of variables with a cut-off: there are
`L` and `A'` such that for every smooth atom `a` on `V` of order `K`, level `j`, radius factor `d`
and constant `A`, and every `y₀ ∈ K₀` within `d 2^(-j)` of its centre, `T a` is a smooth atom on
`Ω` of order `K` with centre `Ψ y₀`, radius factor `2 L d` and constant `A' A`. -/
theorem isSmoothAtom_apply (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    (hint : (interior Ω).Nonempty) (K : ℕ) :
    ∃ L A' : ℝ, 0 ≤ L ∧ 0 ≤ A' ∧ ∀ {d A : ℝ} {j : ℕ} {c : V} {a : V → ℂ}, 0 ≤ A →
      IsSmoothAtom Set.univ K d A j c a → ∀ y₀ ∈ T.K0, ‖y₀ - c‖ ≤ d / 2 ^ j →
        IsSmoothAtom Ω K (2 * L * d) (A' * A) j (T.Psi y₀) (T.apply a) := by
  obtain ⟨L, hL⟩ := T.exists_lipschitzOnWith_Psi hΩ
  obtain ⟨M, hM0, hM⟩ := T.exists_iteratedFDerivWithin_chi_bound hΩ hint K
  obtain ⟨D, hD1, hD⟩ := T.exists_iteratedFDerivWithin_Phi_bound hΩ hint K
  refine ⟨L, K.factorial * 2 ^ K * M * D ^ K, L.coe_nonneg, by positivity,
    fun {d A j c a} hA ha y₀ hy₀ hy₀c => ?_⟩
  set S := Ω ∩ T.U
  have hs : UniqueDiffOn ℝ S := T.uniqueDiffOn_source hΩ hint
  have ht := T.uniqueDiffOn_target hΩ hint
  have hSm : MeasurableSet S := hΩm.inter T.isOpen_U.measurableSet
  have hac : ContDiff ℝ K a := contDiffOn_univ.1 ha.contDiffOn
  set g : V → ℂ := fun z => T.chi z * a z
  have hg : ContDiffOn ℝ K g (Ω ∩ T.U') :=
    (T.contDiffOn_chi.of_le (by exact_mod_cast le_top)).mul hac.contDiffOn
  have hgΦ : ContDiffOn ℝ K (g ∘ T.Phi) S :=
    hg.comp (T.contDiffOn_Phi.of_le (by exact_mod_cast le_top)) T.mapsTo_Phi
  have hEq : ∀ x ∈ S, T.apply a x = (g ∘ T.Phi) x := fun x hx => by
    rw [apply, Set.indicator_of_mem hx]
    rfl
  have hzero : ∀ x ∈ Ω ∩ T.carrierᶜ, T.apply a x = 0 := fun x hx =>
    T.apply_eq_zero_of_notMem a hx.2
  have hopen : IsOpen T.carrierᶜ := T.isCompact_carrier.isClosed.isOpen_compl
  refine ⟨?_, fun x hx => T.apply_eq_zero_of_far hL ha.eq_zero hy₀ hy₀c hx, ?_, ?_⟩
  · -- measurability
    refine (aestronglyMeasurable_indicator_iff hSm).2 ?_
    exact (hgΦ.continuousOn).aestronglyMeasurable hSm
  · -- smoothness within `Ω`
    intro x hx
    by_cases hxc : x ∈ T.carrier
    · have hxS : x ∈ S := T.carrier_subset hxc
      refine (contDiffWithinAt_inter (T.isOpen_U.mem_nhds hxS.2)).1 ?_
      exact (hgΦ x hxS).congr hEq (hEq x hxS)
    · have hev : T.apply a =ᶠ[𝓝[Ω] x] fun _ => 0 :=
        mem_nhdsWithin.2 ⟨T.carrierᶜ, hopen, hxc, fun y hy => hzero y ⟨hy.2, hy.1⟩⟩
      exact contDiffWithinAt_const.congr_of_eventuallyEq hev (hzero x ⟨hx, hxc⟩)
  · -- the derivatives
    intro l hl x hx
    by_cases hxc : x ∈ T.carrier
    · have hxS : x ∈ S := T.carrier_subset hxc
      rw [← iteratedFDerivWithin_inter_open T.isOpen_U hxS.2,
        iteratedFDerivWithin_congr hEq hxS]
      have hC : ∀ i ≤ l, ‖iteratedFDerivWithin ℝ i g (Ω ∩ T.U') (T.Phi x)‖ ≤
          2 ^ l * M * A * 2 ^ (j * l) := fun i hi => by
        refine (T.norm_iteratedFDerivWithin_mul_atom_le hΩ hint hM hA ha (hi.trans hl)
          (T.mapsTo_Phi hxS)).trans ?_
        have h2 : (2 : ℝ) ^ i ≤ 2 ^ l := pow_le_pow_right₀ one_le_two hi
        have h3 : (2 : ℝ) ^ (j * i) ≤ 2 ^ (j * l) :=
          pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_left j hi)
        have := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hM0) hA) h3
          (by positivity) (by positivity)
        simpa [mul_assoc] using this
      have hDi : ∀ i, 1 ≤ i → i ≤ l → ‖iteratedFDerivWithin ℝ i T.Phi S x‖ ≤ D ^ i :=
        fun i hi1 hil => (hD i (hil.trans hl) x hxc).trans (le_self_pow₀ hD1 (by omega))
      refine (norm_iteratedFDerivWithin_comp_le (N := (l : WithTop ℕ∞))
        (hg.of_le (by exact_mod_cast hl)) (T.contDiffOn_Phi.of_le (by exact_mod_cast le_top))
        le_rfl ht hs T.mapsTo_Phi hxS hC hDi).trans ?_
      have hfac : (l.factorial : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_le hl
      have h2 : (2 : ℝ) ^ l ≤ 2 ^ K := pow_le_pow_right₀ one_le_two hl
      have hDl : D ^ l ≤ D ^ K := pow_le_pow_right₀ hD1 hl
      calc (l.factorial : ℝ) * (2 ^ l * M * A * 2 ^ (j * l)) * D ^ l
          = ((l.factorial : ℝ) * 2 ^ l * M * D ^ l) * A * 2 ^ (j * l) := by ring
        _ ≤ ((K.factorial : ℝ) * 2 ^ K * M * D ^ K) * A * 2 ^ (j * l) := by gcongr
        _ = K.factorial * 2 ^ K * M * D ^ K * A * 2 ^ (j * l) := by ring
    · rw [iteratedFDerivWithin_eq_zero_of_eqOn hopen hxc hx (fun y hy => hzero y hy) l, norm_zero]
      positivity

end CutoffDiffeo

end Atoms

end Rd
