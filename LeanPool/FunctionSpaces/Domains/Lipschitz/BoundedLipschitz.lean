/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Extension.LocalExtension
public import LeanPool.FunctionSpaces.Rd.Differences.PointwiseMultipliers
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Bounded Lipschitz domains

A **bounded Lipschitz domain** (Stein; Schneider–Vybíral, Remark 3.2) is a bounded open
set `Ω ⊆ V` whose boundary `Γ` is covered by finitely many open balls `B_j`, centred on `Γ`, with
`B_j ∩ Ω = B_j ∩ Ω_j` for Lipschitz graph domains `Ω_j` (`Rd.BoundedLipschitzDomain`); the free
direction of each graph domain replaces the rotations of the usual definition.

**Restrictions by intrinsic differences**
(`Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn`): for `1 ≤ p < ∞`,
`0 < s < r` and `1 ≤ q ≤ ∞`, `f` agrees on `Ω` with some `F ∈ L_p(V)` with
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`; likewise with the band-limited
approximation spaces (`Rd.BoundedLipschitzDomain.exists_memApprox_extension_iff`). The extension
comes with a bound: its quasi-norm on `V` is at most `C` times the intrinsic one, with `C`
depending only on `Ω`, `p`, `r`, `s` and `q`
(`Rd.BoundedLipschitzDomain.exists_besov_extension_le`).

The proof follows Schneider–Vybíral §3: a covering `ΩBar ⊆ K_0 ∪ ⋃_j K_j` with an inner domain
`K_0`, a smooth resolution of unity, and pointwise multipliers.

* The balls shrink: `Γ ⊆ ⋃_j B(c_j, ρ_j - 2ε)` for some `ε > 0`
  (`Rd.BoundedLipschitzDomain.exists_shrink`), and the points of `Ω` outside these balls keep a
  distance `> 2δ` from `Ωᶜ` (`Rd.BoundedLipschitzDomain.exists_interior_margin`), both by
  compactness; `Ωᶜ` is nonempty in dimension `n ≥ 1`
  (`Rd.BoundedLipschitzDomain.nonempty_compl`). The shrunk balls and the inner patch are bounded
  open sets that cover `ΩBar` (`Rd.BoundedLipschitzDomain.patch`,
  `Rd.BoundedLipschitzDomain.closure_subset_iUnion_patch`). A property that pastes over finite
  covers of `ΩBar` thus passes from the patches to `Ω`
  (`Rd.BoundedLipschitzDomain.exists_of_patches`).
* Local extensions with a bound (`Rd.LocalMeansBump.exists_local_extension_le`) on the boundary
  patches `Ω ∩ B(c_j, ρ_j - 2ε)`, with the cone bump of `Ω_j` rescaled to radius `≤ ε / r`, and on
  the inner patch `{infDist(·, Ωᶜ) > 2δ}`, with a centred bump of radius `≤ δ / r`
  (`Rd.BoundedLipschitzDomain.exists_local_extension_boundary_le`,
  `Rd.BoundedLipschitzDomain.exists_local_extension_interior_le`).
* A smooth resolution of unity subordinate to these patches (Mathlib's
  `SmoothPartitionOfUnity.exists_isSubordinate`, `Rd.exists_smooth_partition`) pastes the local
  extensions (`Rd.exists_pasting_le`, `Rd.indicatorLp_sum_eq_of_partition`, `Rd.ae_sum_mul_eq`),
  by the pointwise multipliers of `Rd.modNorm_mulLp_le` and the triangle inequality
  `Rd.modNorm_finsetSum_le`. The quasi-norm by differences is subadditive and homogeneous
  (`Rd.modNorm_add_le`, `Rd.modNorm_const_smul`).

For a compact set, the smooth resolutions of unity can be chosen equal to `1` on a neighbourhood
of it (`Rd.exists_smooth_partition_nhds`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal Manifold

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### Resolutions of unity -/

section Partition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Smooth resolutions of unity**: for a closed set `s` and a finite open cover `(U_i)` of `s`
there are smooth `ψ_i ≥ 0` with `tsupport ψ_i ⊆ U_i`, `∑_i ψ_i = 1` on `s` and `∑_i ψ_i ≤ 1`
everywhere (Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`). -/
theorem exists_smooth_partition {ι : Type*} [Fintype ι] {s : Set V} (hs : IsClosed s)
    (U : ι → Set V) (hU : ∀ i, IsOpen (U i)) (hcov : s ⊆ ⋃ i, U i) :
    ∃ ψ : ι → V → ℝ, (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧ (∀ x ∈ s, ∑ i, ψ i x = 1) ∧ (∀ i x, 0 ≤ ψ i x) ∧
        ∀ x, ∑ i, ψ i x ≤ 1 := by
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V) hs U hU hcov
  refine ⟨fun i => f i, fun i => contMDiff_iff_contDiff.1 (f i).contMDiff, hf, fun x hx => ?_,
    fun i x => f.nonneg i x, fun x => ?_⟩
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hx
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_le_one x

/-- **Smooth resolutions of unity equal to one near a compact set**: for a compact set `s` and a
finite open cover `(U_i)` of `s` there are smooth `ψ_i ≥ 0` with `tsupport ψ_i ⊆ U_i`,
`∑_i ψ_i = 1` on a neighbourhood of `s` and `∑_i ψ_i ≤ 1` everywhere: `Rd.exists_smooth_partition`
for a compact `L` with `s ⊆ interior L ⊆ L ⊆ ⋃_i U_i` (Mathlib's `exists_compact_between`). -/
theorem exists_smooth_partition_nhds {ι : Type*} [Fintype ι] {s : Set V} (hs : IsCompact s)
    (U : ι → Set V) (hU : ∀ i, IsOpen (U i)) (hcov : s ⊆ ⋃ i, U i) :
    ∃ ψ : ι → V → ℝ, (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧ (∀ᶠ x in 𝓝ˢ s, ∑ i, ψ i x = 1) ∧ (∀ i x, 0 ≤ ψ i x) ∧
        ∀ x, ∑ i, ψ i x ≤ 1 := by
  obtain ⟨L, hL, hsL, hLU⟩ := exists_compact_between hs (isOpen_iUnion hU) hcov
  obtain ⟨ψ, hψ, hψU, hψ1, hψ0, hψle⟩ := exists_smooth_partition hL.isClosed U hU hLU
  exact ⟨ψ, hψ, hψU, eventually_of_mem (isOpen_interior.mem_nhdsSet.2 hsL) fun x hx =>
    hψ1 x (interior_subset hx), hψ0, hψle⟩

end Partition

/-! ### Pasting local extensions -/

section Pasting

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The modulus of a finite sum is at most the sum of the moduli. -/
theorem lpModulus_finsetSum_le {ι : Type*} (t : Finset ι)
    (G : ι → Lp ℂ p (volume : Measure V)) (r k : ℕ) :
    lpModulus p r (∑ i ∈ t, G i) k ≤ ∑ i ∈ t, lpModulus p r (G i) k := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [lpModulus_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (lpModulus_add_le r _ _ k).trans (add_le_add le_rfl ih)

/-- **The Besov quasi-norm by differences of a finite sum** is at most the sum of the quasi-norms:
`‖∑_i G_i‖_p + ‖(2^(ks) ω_r(∑_i G_i, 2^(-k))_p)_k‖_{ℓ_q} ≤
∑_i (‖G_i‖_p + ‖(2^(ks) ω_r(G_i, 2^(-k))_p)_k‖_{ℓ_q})` for `q ≥ 1`
(`Rd.lpModulus_finsetSum_le`, `ENNReal.lqNorm_sum_le`). -/
theorem modNorm_finsetSum_le {ι : Type*} (t : Finset ι)
    (G : ι → Lp ℂ p (volume : Measure V)) (r : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ‖∑ i ∈ t, G i‖ₑ +
        lqNorm q (fun k => dyadicWeight s k * lpModulus p r (∑ i ∈ t, G i) k) ≤
      ∑ i ∈ t, (‖G i‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r (G i) k)) := by
  have h1 : ‖∑ i ∈ t, G i‖ₑ ≤ ∑ i ∈ t, ‖G i‖ₑ := eNorm_sum_le _ _
  have h2 : lqNorm q (fun k => dyadicWeight s k * lpModulus p r (∑ i ∈ t, G i) k) ≤
      ∑ i ∈ t, lqNorm q (fun k => dyadicWeight s k * lpModulus p r (G i) k) :=
    (ENNReal.lqNorm_mono fun k => (mul_le_mul' le_rfl (lpModulus_finsetSum_le t G r k)).trans_eq
      (Finset.mul_sum _ _ _)).trans (ENNReal.lqNorm_sum_le hq _ _)
  rw [Finset.sum_add_distrib]
  exact add_le_add h1 h2

/-- **The Besov quasi-norm by differences is subadditive**:
`‖G + H‖_p + ‖(2^(ks) ω_r(G + H, 2^(-k))_p)_k‖_{ℓ_q} ≤
(‖G‖_p + ‖(2^(ks) ω_r(G, 2^(-k))_p)_k‖_{ℓ_q}) + (‖H‖_p + ‖(2^(ks) ω_r(H, 2^(-k))_p)_k‖_{ℓ_q})`
for `q ≥ 1` (`Rd.lpModulus_add_le`, `ENNReal.lqNorm_add_le`). -/
theorem modNorm_add_le (G H : Lp ℂ p (volume : Measure V)) (r : ℕ) (s : ℝ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    ‖G + H‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r (G + H) k) ≤
      (‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k)) +
        (‖H‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r H k)) := by
  have h2 : lqNorm q (fun k => dyadicWeight s k * lpModulus p r (G + H) k) ≤
      lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k) +
        lqNorm q (fun k => dyadicWeight s k * lpModulus p r H k) :=
    (ENNReal.lqNorm_mono fun k => (mul_le_mul' le_rfl (lpModulus_add_le r G H k)).trans_eq
      (mul_add _ _ _)).trans (ENNReal.lqNorm_add_le hq _ _)
  rw [add_add_add_comm]
  exact add_le_add (eNorm_add_le G H) h2

/-- **The Besov quasi-norm by differences is homogeneous**:
`‖c G‖_p + ‖(2^(ks) ω_r(c G, 2^(-k))_p)_k‖_{ℓ_q} =
|c| (‖G‖_p + ‖(2^(ks) ω_r(G, 2^(-k))_p)_k‖_{ℓ_q})`
(`Rd.lpModulus_const_smul`, `ENNReal.lqNorm_const_mul`). -/
theorem modNorm_const_smul (c : ℂ) (G : Lp ℂ p (volume : Measure V)) (r : ℕ) (s : ℝ)
    (q : ℝ≥0∞) :
    ‖c • G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r (c • G) k) =
      ‖c‖ₑ * (‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k)) := by
  simp_rw [lpModulus_const_smul, mul_left_comm (dyadicWeight s _) ‖c‖ₑ]
  rw [ENNReal.lqNorm_const_mul, eNorm_smul, mul_add]

/-- **Finite sums keep the Besov spaces by differences** (`Rd.modNorm_finsetSum_le`). -/
theorem modNorm_finsetSum_lt_top {ι : Type*} (t : Finset ι)
    (G : ι → Lp ℂ p (volume : Measure V)) {r : ℕ} {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hG : ∀ i ∈ t, ‖G i‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r (G i) k) < ∞) :
    ‖∑ i ∈ t, G i‖ₑ +
        lqNorm q (fun k => dyadicWeight s k * lpModulus p r (∑ i ∈ t, G i) k) < ∞ :=
  (modNorm_finsetSum_le t G r s hq).trans_lt (ENNReal.sum_lt_top.2 hG)

/-- **The pasted functions agree with `f`**: if `∑_i ψ_i = 1` on `O`, `tsupport ψ_i ⊆ U_i` and
`F_i = f` almost everywhere on `O ∩ U_i`, then `∑_i ψ_i F_i = f` almost everywhere on `O`. -/
theorem ae_sum_mul_eq {ι : Type*} [Fintype ι] {O : Set V} {U : ι → Set V} {ψ : ι → V → ℝ}
    (hψU : ∀ i, tsupport (ψ i) ⊆ U i) (hψ1 : ∀ x ∈ O, ∑ i, ψ i x = 1) {F : ι → V → ℂ}
    {f : V → ℂ} (hFf : ∀ i, ∀ᵐ x ∂volume, x ∈ O ∩ U i → F i x = f x) :
    ∀ᵐ x ∂volume, x ∈ O → ∑ i, (ψ i x : ℂ) * F i x = f x := by
  filter_upwards [ae_all_iff.2 hFf] with x h2 hxO
  have hterm : ∀ i, (ψ i x : ℂ) * F i x = (ψ i x : ℂ) * f x := fun i => by
    by_cases hψx : ψ i x = 0
    · simp [hψx]
    · rw [h2 i ⟨hxO, hψU i (subset_tsupport _ hψx)⟩]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hψ1 x hxO, Complex.ofReal_one, one_mul]

/-- **Pasting with a resolution of unity agrees with `f` on `O`**: if `∑_i ψ_i = 1` on `O`,
`ψ_i` vanishes outside `U_i`, `G_i = ψ_i F_i` almost everywhere and `F_i = f` almost everywhere
on `O ∩ U_i`, then `∑_i G_i = f` almost everywhere on `O`. -/
theorem indicatorLp_sum_eq_of_partition {ι : Type*} [Fintype ι] {O : Set V}
    (hO : MeasurableSet O) (U : ι → Set V) (ψ : ι → V → ℝ) (hψU : ∀ i, Function.support (ψ i) ⊆ U i)
    (hψ1 : ∀ x ∈ O, ∑ i, ψ i x = 1) (f : Lp ℂ p (volume : Measure V))
    (F G : ι → Lp ℂ p (volume : Measure V))
    (hG : ∀ i, G i =ᵐ[volume] fun x => ((ψ i x : ℝ) : ℂ) * F i x)
    (hFf : ∀ i, ∀ᵐ x ∂(volume : Measure V), x ∈ O → x ∈ U i → F i x = f x) :
    indicatorLp hO (∑ i, G i) = indicatorLp hO f := by
  refine Lp.ext ?_
  have hall : ∀ᵐ x ∂(volume : Measure V), ∀ i, (x ∈ O → x ∈ U i → F i x = f x) ∧
      G i x = ((ψ i x : ℝ) : ℂ) * F i x :=
    ae_all_iff.2 fun i => (hFf i).and (hG i)
  filter_upwards [indicatorLp_apply_ae hO (∑ i, G i), indicatorLp_apply_ae hO f,
    Lp.coeFn_fun_finsetSum Finset.univ G, hall] with x h1 h2 h3 h4
  rw [h1, h2]
  by_cases hx : x ∈ O
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h3]
    have hterm : ∀ i, G i x = ((ψ i x : ℝ) : ℂ) * f x := fun i => by
      rw [(h4 i).2]
      by_cases hψx : ψ i x = 0
      · simp [hψx]
      · rw [(h4 i).1 hx (hψU i hψx)]
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hψ1 x hx, Complex.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- **Pasting local extensions with a bound**: let `(U_i)` be a finite cover of `Ō` by bounded
open sets. There is `C < ∞` such that for all `f` and all `F_i` that agree with `f` almost
everywhere on `O ∩ U_i`, `f` agrees on `O` with some `G` with
`‖G‖_p + ‖(2^(ks) ω_r(G, 2^(-k))_p)_k‖_{ℓ_q} ≤`
`C ∑_i (‖F_i‖_p + ‖(2^(ks) ω_r(F_i, 2^(-k))_p)_k‖_{ℓ_q})`.
The resolution of unity `(ψ_i)` subordinate to `(U_i)` (`Rd.exists_smooth_partition`) and the
bounds on its derivatives (`Rd.exists_iteratedFDeriv_bound`) are fixed before `f`; `G = ∑_i ψ_i F_i`
and `C` is the sum of the multiplier constants of `Rd.modNorm_mulLp_le` (`Rd.multiplierTotal`). -/
theorem exists_pasting_le {ι : Type*} [Fintype ι] (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {O : Set V} (hO : MeasurableSet O) (U : ι → Set V)
    (hUo : ∀ i, IsOpen (U i)) (hUb : ∀ i, Bornology.IsBounded (U i))
    (hcov : closure O ⊆ ⋃ i, U i) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (f : Lp ℂ p (volume : Measure V))
      (F : ι → Lp ℂ p (volume : Measure V)),
      (∀ i, ∀ᵐ x ∂(volume : Measure V), x ∈ O → x ∈ U i → F i x = f x) →
      ∃ G : Lp ℂ p (volume : Measure V), indicatorLp hO G = indicatorLp hO f ∧
        ‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k) ≤
          C * ∑ i, (‖F i‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r (F i) k)) := by
  obtain ⟨ψ, hψ, hψU, hψ1, -⟩ := exists_smooth_partition isClosed_closure U hUo hcov
  set ψC : ι → V → ℂ := fun i x => ((ψ i x : ℝ) : ℂ)
  have hψC : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψC i) := fun i =>
    Complex.ofRealCLM.contDiff.comp (hψ i)
  have hcs : ∀ i, HasCompactSupport (ψC i) := fun i =>
    (isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      ((hUb i).subset (hψU i))).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_comp_subset Complex.ofReal_zero _)
  choose C hC using fun i => exists_iteratedFDeriv_bound (hψC i) (hcs i) r
  refine ⟨∑ i, multiplierTotal (V := V) hp r s (C i),
    ENNReal.sum_ne_top.2 fun i _ => multiplierTotal_ne_top hp hsr (C i), fun f F hFf => ?_⟩
  set G : ι → Lp ℂ p (volume : Measure V) := fun i =>
    mulLp (hψC i).continuous (norm_le_of_iteratedFDeriv_le (hC i)) (F i)
  refine ⟨∑ i, G i, indicatorLp_sum_eq_of_partition hO U ψ
    (fun i => (subset_tsupport _).trans (hψU i)) (fun x hx => hψ1 x (subset_closure hx)) f F G
    (fun i => mulLp_apply_ae _ _ (F i)) hFf,
    (modNorm_finsetSum_le _ G r s hq).trans ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => (modNorm_mulLp_le hp (hψC i) (hC i) hsr hq (F i)).trans
    (mul_le_mul' (Finset.single_le_sum (f := fun i => multiplierTotal (V := V) hp r s (C i))
      (fun _ _ => zero_le) (Finset.mem_univ i)) le_rfl)

/-- **Pasting local extensions**: let `(U_i)` be a finite cover of `Ō` by bounded open sets and
`F_i` functions with finite Besov quasi-norms by differences that agree with `f` almost everywhere
on `O ∩ U_i`. Then `f` agrees on `O` with a function with a finite Besov quasi-norm: `∑_i ψ_i F_i`
for a smooth resolution of unity `(ψ_i)` subordinate to `(U_i)` (`Rd.exists_pasting_le`). -/
theorem exists_pasting {ι : Type*} [Finite ι] (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {O : Set V} (hO : MeasurableSet O) (U : ι → Set V)
    (hUo : ∀ i, IsOpen (U i)) (hUb : ∀ i, Bornology.IsBounded (U i))
    (hcov : closure O ⊆ ⋃ i, U i) (f : Lp ℂ p (volume : Measure V))
    (F : ι → Lp ℂ p (volume : Measure V))
    (hF : ∀ i, ‖F i‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r (F i) k) < ∞)
    (hFf : ∀ i, ∀ᵐ x ∂(volume : Measure V), x ∈ O → x ∈ U i → F i x = f x) :
    ∃ G : Lp ℂ p (volume : Measure V), indicatorLp hO G = indicatorLp hO f ∧
      ‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k) < ∞ := by
  let := Fintype.ofFinite ι
  obtain ⟨C, hC, h⟩ := exists_pasting_le hp hsr hq hO U hUo hUb hcov
  obtain ⟨G, hG, hle⟩ := h f F hFf
  exact ⟨G, hG, hle.trans_lt (ENNReal.mul_lt_top hC.lt_top (ENNReal.sum_lt_top.2 fun i _ => hF i))⟩

end Pasting

/-! ### Bounded Lipschitz domains -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- In finite dimension the **frontier of a bounded set is compact**: it is a closed subset of the
compact closure (Mathlib's `Bornology.IsBounded.isCompact_closure`). -/
theorem isCompact_frontier_of_isBounded [FiniteDimensional ℝ V] {s : Set V}
    (hs : Bornology.IsBounded s) : IsCompact (frontier s) :=
  hs.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure

variable (V) in
/-- A **bounded Lipschitz domain** (Stein; Schneider–Vybíral, Remark 3.2): a bounded open
set whose boundary is covered by finitely many open balls `B_j`, centred on the boundary, with
`B_j ∩ Ω = B_j ∩ Ω_j` for Lipschitz graph domains `Ω_j`; the free direction of each graph domain
replaces the rotations of the usual definition. The structure carries the balls and the graph
domains as data; in finite dimension every set satisfying the usual definition
(`Rd.IsBoundedLipschitzDomain`) is the carrier of one
(`Rd.BoundedLipschitzDomain.ofIsBoundedLipschitzDomain`, `Rd.isBoundedLipschitzDomain_iff_exists`),
every open ball and every bounded open convex set among them (`Rd.BoundedLipschitzDomain.ball`,
`Rd.BoundedLipschitzDomain.ofConvex`, from `Rd.isBoundedLipschitzDomain_of_convex`). -/
structure BoundedLipschitzDomain where
  /-- The domain. -/
  carrier : Set V
  isOpen : IsOpen carrier
  isBounded : Bornology.IsBounded carrier
  /-- The number of boundary balls. -/
  N : ℕ
  /-- The centres of the boundary balls. -/
  center : Fin N → V
  /-- The radii of the boundary balls. -/
  radius : Fin N → ℝ
  radius_pos : ∀ j, 0 < radius j
  center_mem : ∀ j, center j ∈ frontier carrier
  /-- The Lipschitz graph domains of the boundary balls. -/
  graph : Fin N → LipschitzGraph V
  frontier_subset : frontier carrier ⊆ ⋃ j, ball (center j) (radius j)
  ball_inter : ∀ j, ball (center j) (radius j) ∩ carrier =
    ball (center j) (radius j) ∩ (graph j).domain

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- On a concentric ball of smaller radius the domain is the graph domain. -/
theorem inter_ball_eq (j : Fin Ω.N) {ρ : ℝ} (hρ : ρ ≤ Ω.radius j) :
    Ω.carrier ∩ ball (Ω.center j) ρ = (Ω.graph j).domain ∩ ball (Ω.center j) ρ := by
  ext x
  constructor
  · rintro ⟨hx, hxb⟩
    have h : x ∈ ball (Ω.center j) (Ω.radius j) ∩ Ω.carrier := ⟨ball_subset_ball hρ hxb, hx⟩
    rw [Ω.ball_inter j] at h
    exact ⟨h.2, hxb⟩
  · rintro ⟨hx, hxb⟩
    have h : x ∈ ball (Ω.center j) (Ω.radius j) ∩ (Ω.graph j).domain :=
      ⟨ball_subset_ball hρ hxb, hx⟩
    rw [← Ω.ball_inter j] at h
    exact ⟨h.2, hxb⟩

variable [FiniteDimensional ℝ V]

/-- The closure of a bounded Lipschitz domain is compact. -/
theorem isCompact_closure : IsCompact (closure Ω.carrier) := Ω.isBounded.isCompact_closure

/-- The boundary of a bounded Lipschitz domain is compact. -/
theorem isCompact_frontier : IsCompact (frontier Ω.carrier) :=
  isCompact_frontier_of_isBounded Ω.isBounded

/-- **Shrinking the boundary balls**: `Γ ⊆ ⋃_j B(c_j, ρ_j - 2ε)` for some `ε > 0`, by
compactness of `Γ`. -/
theorem exists_shrink :
    ∃ ε : ℝ, 0 < ε ∧ frontier Ω.carrier ⊆ ⋃ j, ball (Ω.center j) (Ω.radius j - 2 * ε) := by
  set O : ℕ → Set V := fun n => ⋃ j, ball (Ω.center j) (Ω.radius j - 1 / ((n : ℝ) + 1))
  have hmono : Monotone O := fun m n hmn => Set.iUnion_mono fun j => ball_subset_ball (by
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    linarith)
  have hcover : frontier Ω.carrier ⊆ ⋃ n, O n := fun x hx => by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (Ω.frontier_subset hx)
    rw [mem_ball] at hj
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hj)
    exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨j, by rw [mem_ball]; linarith⟩⟩
  obtain ⟨n, hn⟩ := Ω.isCompact_frontier.elim_directed_cover O
    (fun n => isOpen_iUnion fun j => isOpen_ball) hcover hmono.directed_le
  refine ⟨1 / (2 * ((n : ℝ) + 1)), by positivity, hn.trans fun x hx => ?_⟩
  have h2 : 2 * (1 / (2 * ((n : ℝ) + 1))) = 1 / ((n : ℝ) + 1) := by field_simp
  rw [h2]
  exact hx

omit [FiniteDimensional ℝ V] in
/-- In dimension `n ≥ 1` the complement of a bounded Lipschitz domain is nonempty, since `V` is
unbounded (Mathlib's `NormedSpace.unbounded_univ`). -/
theorem nonempty_compl [Nontrivial V] : (Ω.carrierᶜ).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
  exact NormedSpace.unbounded_univ ℝ V (h ▸ Ω.isBounded)

/-- **The interior margin**: if `Ωᶜ` is nonempty and `Γ ⊆ ⋃_j B(c_j, ρ_j - 2ε)`, the points of
`Ω` outside these balls have distance `> 2δ` from `Ωᶜ` for some `δ > 0`, by compactness. -/
theorem exists_interior_margin (hc : (Ω.carrierᶜ).Nonempty) {ε : ℝ}
    (hε : frontier Ω.carrier ⊆ ⋃ j, ball (Ω.center j) (Ω.radius j - 2 * ε)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ω.carrier, (∀ j, x ∉ ball (Ω.center j) (Ω.radius j - 2 * ε)) →
      2 * δ < infDist x Ω.carrierᶜ := by
  set K := closure Ω.carrier \ ⋃ j, ball (Ω.center j) (Ω.radius j - 2 * ε)
  have hK : IsCompact K := Ω.isCompact_closure.diff (isOpen_iUnion fun j => isOpen_ball)
  have hKΩ : K ⊆ Ω.carrier := fun x ⟨hx, hxb⟩ => by
    have hxf : x ∉ frontier Ω.carrier := fun h => hxb (hε h)
    have : x ∈ closure Ω.carrier \ frontier Ω.carrier := ⟨hx, hxf⟩
    rwa [closure_sdiff_frontier, Ω.isOpen.interior_eq] at this
  have hpos : ∀ x ∈ Ω.carrier, 0 < infDist x Ω.carrierᶜ := fun x hx =>
    (Ω.isOpen.isClosed_compl.notMem_iff_infDist_pos hc).1 fun h => h hx
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun x hx hxb => ?_⟩
    have : x ∈ K := ⟨subset_closure hx, by simpa using hxb⟩
    rw [hK0] at this
    exact this.elim
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_infDist_pt _).continuousOn
    refine ⟨infDist x₀ Ω.carrierᶜ / 4, by linarith [hpos x₀ (hKΩ hx₀)], fun x hx hxb => ?_⟩
    have hxK : x ∈ K := ⟨subset_closure hx, by simpa using hxb⟩
    have h1 := hmin hxK
    have h2 := hpos x₀ (hKΩ hx₀)
    simp only [Set.mem_ofPred_eq] at h1
    linarith

/-- The **patches** of `Ω` for `ε, δ`: the inner patch `{infDist(·, Ωᶜ) > 2δ}` (index `none`) and
the shrunk boundary balls `B(c_j, ρ_j - 2ε)` (index `some j`). -/
def patch (ε δ : ℝ) (i : Option (Fin Ω.N)) : Set V :=
  i.elim {x : V | 2 * δ < infDist x Ω.carrierᶜ} fun j => ball (Ω.center j) (Ω.radius j - 2 * ε)

omit [FiniteDimensional ℝ V] in
/-- The patches are open. -/
theorem isOpen_patch (ε δ : ℝ) (i : Option (Fin Ω.N)) : IsOpen (Ω.patch ε δ i) := by
  cases i with
  | none => exact isOpen_lt continuous_const (continuous_infDist_pt _)
  | some j => exact isOpen_ball

omit [FiniteDimensional ℝ V] in
/-- The patches are bounded for `δ ≥ 0`: the inner patch lies in `Ω`
(`Rd.setOf_lt_infDist_compl_subset`). -/
theorem isBounded_patch (ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (i : Option (Fin Ω.N)) :
    Bornology.IsBounded (Ω.patch ε δ i) := by
  cases i with
  | none => exact Ω.isBounded.subset (setOf_lt_infDist_compl_subset _ (by positivity))
  | some j => exact isBounded_ball

omit [FiniteDimensional ℝ V] in
/-- **The patches cover `ΩBar`** if the shrunk balls cover `Γ` and the points of `Ω` outside them
have distance `> 2δ` from `Ωᶜ` (`Rd.BoundedLipschitzDomain.exists_shrink`,
`Rd.BoundedLipschitzDomain.exists_interior_margin`). -/
theorem closure_subset_iUnion_patch {ε δ : ℝ}
    (hε : frontier Ω.carrier ⊆ ⋃ j, ball (Ω.center j) (Ω.radius j - 2 * ε))
    (hδ : ∀ x ∈ Ω.carrier, (∀ j, x ∉ ball (Ω.center j) (Ω.radius j - 2 * ε)) →
      2 * δ < infDist x Ω.carrierᶜ) :
    closure Ω.carrier ⊆ ⋃ i, Ω.patch ε δ i := by
  intro x hx
  by_cases hxf : x ∈ frontier Ω.carrier
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hε hxf)
    exact Set.mem_iUnion.2 ⟨some j, hj⟩
  · have hxΩ : x ∈ Ω.carrier := by
      have : x ∈ closure Ω.carrier \ frontier Ω.carrier := ⟨hx, hxf⟩
      rwa [closure_sdiff_frontier, Ω.isOpen.interior_eq] at this
    by_cases hxb : ∃ j, x ∈ ball (Ω.center j) (Ω.radius j - 2 * ε)
    · obtain ⟨j, hj⟩ := hxb
      exact Set.mem_iUnion.2 ⟨some j, hj⟩
    · push Not at hxb
      exact Set.mem_iUnion.2 ⟨none, hδ x hxΩ hxb⟩

/-- **Pasting over the patches**: let `P U C` be a property of a set `U ⊆ V` and a constant
`C ∈ [0, ∞]` that passes from the sets `Ω ∩ U_i` of every cover `(U_i)_{i ∈ {0, …, N}}` of `ΩBar` by
`N + 1` bounded open sets, one for each boundary ball and one inner set (indexed by
`Option (Fin Ω.N)`), with finite constants, to `Ω`, with a finite constant. If `P` holds with a
finite constant for every boundary patch `Ω ∩ B(c_j, ρ_j - 2ε)`, `ε > 0`, and for every inner
patch `Ω ∩ {infDist(·, Ωᶜ) > 2δ}`, `δ > 0`, then it holds for `Ω` with a finite constant: for
suitable `ε` and `δ` the patches `Rd.BoundedLipschitzDomain.patch` cover `ΩBar`
(`Rd.BoundedLipschitzDomain.exists_shrink`, `Rd.BoundedLipschitzDomain.exists_interior_margin`,
`Rd.BoundedLipschitzDomain.closure_subset_iUnion_patch`). -/
theorem exists_of_patches [Nontrivial V] (P : Set V → ℝ≥0∞ → Prop)
    (hcover : ∀ U : Option (Fin Ω.N) → Set V, (∀ i, IsOpen (U i)) →
      (∀ i, Bornology.IsBounded (U i)) → closure Ω.carrier ⊆ ⋃ i, U i →
      ∀ C : Option (Fin Ω.N) → ℝ≥0∞, (∀ i, C i ≠ ∞) → (∀ i, P (Ω.carrier ∩ U i) (C i)) →
        ∃ C' : ℝ≥0∞, C' ≠ ∞ ∧ P Ω.carrier C')
    (hbd : ∀ ε : ℝ, 0 < ε → ∀ j : Fin Ω.N, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      P (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) C)
    (hin : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      P (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}) C) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ P Ω.carrier C := by
  obtain ⟨ε, hε0, hε⟩ := Ω.exists_shrink
  obtain ⟨δ, hδ0, hδ⟩ := Ω.exists_interior_margin Ω.nonempty_compl hε
  choose Cb hCb hb using hbd ε hε0
  obtain ⟨C0, hC0, h0⟩ := hin δ hδ0
  refine hcover (Ω.patch ε δ) (Ω.isOpen_patch ε δ) (Ω.isBounded_patch ε hδ0.le)
    (Ω.closure_subset_iUnion_patch hε hδ) (fun i => i.elim C0 Cb) (fun i => ?_) (fun i => ?_)
  · cases i with
    | none => exact hC0
    | some j => exact hCb j
  · cases i with
    | none => exact h0
    | some j => exact hb j

variable [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [FiniteDimensional ℝ V] in
/-- A bounded Lipschitz domain is measurable. -/
theorem measurableSet : MeasurableSet Ω.carrier := Ω.isOpen.measurableSet

/-- The intrinsic quasi-norm of `f` on a measurable `T ⊆ Ω` is at most that on `Ω`
(`Rd.modNormOn_mono_set`). -/
theorem modNormOn_mono_set {T : Set V} (hT : MeasurableSet T) (hTΩ : T ⊆ Ω.carrier) (r : ℕ)
    (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) :
    modNormOn hT r s q f ≤ modNormOn Ω.measurableSet r s q f :=
  Rd.modNormOn_mono_set hT Ω.measurableSet hTΩ r s q f

/-- **The boundary patches with a bound**: there is `C < ∞` such that on `Ω ∩ B(c_j, ρ_j - 2ε)`
every `f` with `N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` agrees with a
function `F` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C N_Ω(f)`, by the local extension
with the cone bump of `Ω_j` rescaled to radius `≤ ε / r`
(`Rd.LipschitzGraph.exists_coneBump_radius_le`, `Rd.LocalMeansBump.exists_local_extension_le`);
the bump and `C` depend only on `ε`, `r`, `s` and `j`. -/
theorem exists_local_extension_boundary_le (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) {s : ℝ}
    (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) (j : Fin Ω.N) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn Ω.measurableSet r s q f < ∞ →
      ∃ F : Lp ℂ p (volume : Measure V),
        ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
            C * modNormOn Ω.measurableSet r s q f ∧
          ∀ᵐ x ∂(volume : Measure V), x ∈ Ω.carrier →
            x ∈ ball (Ω.center j) (Ω.radius j - 2 * ε) → F x = f x := by
  set G := Ω.graph j
  set c := Ω.center j
  set ρ := Ω.radius j
  obtain ⟨b, hb, hR, hLR⟩ := G.exists_coneBump_radius_le (Nat.cast_nonneg r) hε
  have hU : MeasurableSet (G.domain ∩ ball c (ρ - 2 * ε)) :=
    (G.isOpen_domain.inter isOpen_ball).measurableSet
  have hW : MeasurableSet (G.domain ∩ ball c (ρ - ε)) :=
    (G.isOpen_domain.inter isOpen_ball).measurableSet
  have hT : MeasurableSet (G.domain ∩ ball c ρ) :=
    (G.isOpen_domain.inter isOpen_ball).measurableSet
  have hTΩ : G.domain ∩ ball c ρ ⊆ Ω.carrier := by
    rw [← Ω.inter_ball_eq j le_rfl]
    exact Set.inter_subset_left
  refine ⟨b.localExtConst r s, b.localExtConst_ne_top hs hsr, fun f hf => ?_⟩
  obtain ⟨F, hF, hFf⟩ := b.exists_local_extension_le hp hr hs hq hU hW hT
    (Set.inter_subset_inter_right _ (ball_subset_ball (by linarith))) (G.patch_support hb hLR)
    (G.patch_step hb hLR) hR f ((Ω.modNormOn_mono_set hT hTΩ r s q f).trans_lt hf)
  refine ⟨F, hF.trans (mul_le_mul' le_rfl (Ω.modNormOn_mono_set hT hTΩ r s q f)), ?_⟩
  filter_upwards [Lp.ext_iff.1 hFf, indicatorLp_apply_ae hU F, indicatorLp_apply_ae hU f]
    with x h1 h2 h3 hxΩ hxb
  have hxU : x ∈ G.domain ∩ ball c (ρ - 2 * ε) := by
    rw [← Ω.inter_ball_eq j (by linarith)]
    exact ⟨hxΩ, hxb⟩
  rw [h2, h3, Set.indicator_of_mem hxU, Set.indicator_of_mem hxU] at h1
  exact h1

/-- **The boundary patches**: on `Ω ∩ B(c_j, ρ_j - 2ε)`, `f` agrees with a function with a finite
Besov quasi-norm on `V`, by the local extension with the cone bump of `Ω_j` rescaled to radius
`≤ ε / r` (`Rd.BoundedLipschitzDomain.exists_local_extension_boundary_le`). -/
theorem exists_local_extension_boundary (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) (j : Fin Ω.N)
    (f : Lp ℂ p (volume : Measure V))
    (hf : modNormOn Ω.measurableSet r s q f < ∞) :
    ∃ F : Lp ℂ p (volume : Measure V),
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) < ∞ ∧
        ∀ᵐ x ∂(volume : Measure V), x ∈ Ω.carrier →
          x ∈ ball (Ω.center j) (Ω.radius j - 2 * ε) → F x = f x := by
  obtain ⟨C, hC, h⟩ := Ω.exists_local_extension_boundary_le hp hr hs hsr hq hε j
  obtain ⟨F, hF, hFf⟩ := h f hf
  exact ⟨F, hF.trans_lt (ENNReal.mul_lt_top hC.lt_top hf), hFf⟩

/-- **The inner patch with a bound**: there is `C < ∞` such that on `{infDist(·, Ωᶜ) > 2δ}` every
`f` with `N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` agrees with a
function `F` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C N_Ω(f)`, by the local extension
with a centred bump of radius `≤ δ / r` (`Rd.LocalMeansBump.exists_local_extension_le`); the bump
and `C` depend only on `δ`, `r` and `s`. -/
theorem exists_local_extension_interior_le (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) {s : ℝ}
    (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn Ω.measurableSet r s q f < ∞ →
      ∃ F : Lp ℂ p (volume : Measure V),
        ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
            C * modNormOn Ω.measurableSet r s q f ∧
          ∀ᵐ x ∂(volume : Measure V), x ∈ Ω.carrier →
            x ∈ {x : V | 2 * δ < infDist x Ω.carrierᶜ} → F x = f x := by
  have hR0 : 0 < min (1 / 2 : ℝ) (δ / ((r : ℝ) + 1)) := lt_min (by norm_num) (by positivity)
  set b := LocalMeansBump.centered (V := V) hR0
  have hR : b.radius ≤ 1 / 2 := min_le_left _ _
  have hLR : (r : ℝ) * b.radius ≤ δ := by
    calc (r : ℝ) * b.radius ≤ r * (δ / ((r : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg r)
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith
  have hU := measurableSet_infDist_gt Ω.carrier (2 * δ)
  have hW := measurableSet_infDist_gt Ω.carrier δ
  refine ⟨b.localExtConst r s, b.localExtConst_ne_top hs hsr, fun f hf => ?_⟩
  obtain ⟨F, hF, hFf⟩ := b.exists_local_extension_le hp hr hs hq hU hW Ω.measurableSet
    (setOf_lt_infDist_compl_subset _ (by positivity))
    (fun x hx j y hy => interior_patch_support Ω.carrier
      (fun y hy => (not_lt.1 fun h => hy (b.dual_eq_zero r j h)).trans hLR) x hx y hy)
    (fun c hc z hz => interior_patch_step Ω.carrier (by
      have hz' : ‖z‖ ≤ b.radius := not_lt.1 fun h => hz (b.eq_zero z h)
      have hc0 : 0 < c := zero_lt_one.trans_le hc
      have hnorm : ‖-c⁻¹ • z‖ ≤ b.radius := by
        rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hc0.le]
        calc c⁻¹ * ‖z‖ ≤ 1 * ‖z‖ :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hc) (norm_nonneg z)
          _ ≤ b.radius := by rw [one_mul]; exact hz'
      exact (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg r)).trans hLR))
    hR f hf
  refine ⟨F, hF, ?_⟩
  filter_upwards [Lp.ext_iff.1 hFf, indicatorLp_apply_ae hU F, indicatorLp_apply_ae hU f]
    with x h1 h2 h3 _ hxU
  have hxU' : x ∈ {x : V | 2 * δ < infDist x Ω.carrierᶜ} := hxU
  rw [h2, h3, Set.indicator_of_mem hxU', Set.indicator_of_mem hxU'] at h1
  exact h1

/-- **The inner patch**: on `{infDist(·, Ωᶜ) > 2δ}`, `f` agrees with a function with a finite
Besov quasi-norm on `V`, by the local extension with a centred bump of radius `≤ δ / r`
(`Rd.BoundedLipschitzDomain.exists_local_extension_interior_le`). -/
theorem exists_local_extension_interior (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {δ : ℝ} (hδ : 0 < δ) (f : Lp ℂ p (volume : Measure V))
    (hf : modNormOn Ω.measurableSet r s q f < ∞) :
    ∃ F : Lp ℂ p (volume : Measure V),
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) < ∞ ∧
        ∀ᵐ x ∂(volume : Measure V), x ∈ Ω.carrier →
          x ∈ {x : V | 2 * δ < infDist x Ω.carrierᶜ} → F x = f x := by
  obtain ⟨C, hC, h⟩ := Ω.exists_local_extension_interior_le hp hr hs hsr hq hδ
  obtain ⟨F, hF, hFf⟩ := h f hf
  exact ⟨F, hF.trans_lt (ENNReal.mul_lt_top hC.lt_top hf), hFf⟩

/-- **On the whole space the intrinsic quasi-norm is the quasi-norm on `V`**: if `Ω = V`
(possible only for `V = {0}`, since `Ω` is bounded), then
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}`
`= ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}` (`Rd.modNormOn_univ`). -/
theorem modNorm_eq_modNormOn_of_carrier_eq_univ (hu : Ω.carrier = Set.univ) (r : ℕ) (s : ℝ)
    (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) =
      modNormOn Ω.measurableSet r s q f :=
  (modNormOn_univ r s q f).symm.trans
    (modNormOn_congr_set MeasurableSet.univ Ω.measurableSet (by rw [hu]) r s q f)

/-- **The extension for bounded Lipschitz domains with a bound** (Rychkov): for `1 ≤ p < ∞`,
`0 < s < r` and `1 ≤ q ≤ ∞` there is `C < ∞` such that every `f` with
`N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` agrees on
`Ω` with some `F` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C N_Ω(f)`. The patches, the
bumps of the local extensions and the resolution of unity depend only on `Ω` and `r`, so `C`
is fixed before `f`: it is the pasting constant times the sum of the local constants
(`Rd.exists_pasting_le`, `Rd.BoundedLipschitzDomain.exists_local_extension_boundary_le`,
`Rd.BoundedLipschitzDomain.exists_local_extension_interior_le`; for `V = {0}`, where `Ω = V`,
`C = 1`). Every step is linear in `f`, so for fixed `r` the construction is a bounded linear
operator, as in Rychkov; this theorem records its bound for each `f`. -/
theorem exists_besov_extension_le (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn Ω.measurableSet r s q f < ∞ →
      ∃ F : Lp ℂ p (volume : Measure V), indicatorLp Ω.measurableSet F =
          indicatorLp Ω.measurableSet f ∧
        ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
          C * modNormOn Ω.measurableSet r s q f := by
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (Nat.cast_pos.1 (hs.trans hsr)).ne'
  rcases (Ω.carrierᶜ).eq_empty_or_nonempty with hc | hc
  · -- `Ω = V`
    refine ⟨1, ENNReal.one_ne_top, fun f _ => ⟨f, rfl, ?_⟩⟩
    rw [one_mul, Ω.modNorm_eq_modNormOn_of_carrier_eq_univ (Set.compl_empty_iff.1 hc)]
  obtain ⟨ε, hε0, hε⟩ := Ω.exists_shrink
  obtain ⟨δ, hδ0, hδ⟩ := Ω.exists_interior_margin hc hε
  choose Cb hCb hextb using fun j => Ω.exists_local_extension_boundary_le hp hr hs hsr hq hε0 j
  obtain ⟨C0, hC0, hext0⟩ := Ω.exists_local_extension_interior_le hp hr hs hsr hq hδ0
  obtain ⟨Cp, hCp, hpaste⟩ := exists_pasting_le (ι := Option (Fin Ω.N)) hp hsr hq
    Ω.measurableSet (Ω.patch ε δ) (Ω.isOpen_patch ε δ) (Ω.isBounded_patch ε hδ0.le)
    (Ω.closure_subset_iUnion_patch hε hδ)
  set Cl : Option (Fin Ω.N) → ℝ≥0∞ := fun i => i.elim C0 Cb
  have hCl : ∀ i, Cl i ≠ ∞ := fun i => by
    cases i with
    | none => exact hC0
    | some j => exact hCb j
  refine ⟨Cp * ∑ i, Cl i, ENNReal.mul_ne_top hCp (ENNReal.sum_ne_top.2 fun i _ => hCl i),
    fun f hf => ?_⟩
  choose Fb hFb hFbf using fun j => hextb j f hf
  obtain ⟨F0, hF0, hF0f⟩ := hext0 f hf
  obtain ⟨G, hG, hGle⟩ := hpaste f (fun i => i.elim F0 Fb) fun i => by
    cases i with
    | none => exact hF0f
    | some j => exact hFbf j
  refine ⟨G, hG, hGle.trans ?_⟩
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => ?_)
  cases i with
  | none => exact hF0
  | some j => exact hFb j

/-- **The extension for bounded Lipschitz domains**: for `1 ≤ p < ∞`, `0 < s < r` and
`1 ≤ q ≤ ∞`, if `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`, then `f` agrees on
`Ω` with a function with a finite Besov quasi-norm by differences on `V`
(`Rd.BoundedLipschitzDomain.exists_besov_extension_le`). -/
theorem exists_besov_extension_of_modulusOn (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : modNormOn Ω.measurableSet r s q f < ∞) :
    ∃ F : Lp ℂ p (volume : Measure V), indicatorLp Ω.measurableSet F =
        indicatorLp Ω.measurableSet f ∧
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) < ∞ := by
  obtain ⟨C, hC, h⟩ := Ω.exists_besov_extension_le hp hs hsr hq
  obtain ⟨F, hFf, hF⟩ := h f hf
  exact ⟨F, hFf, hF.trans_lt (ENNReal.mul_lt_top hC.lt_top hf)⟩

/-- **Restrictions of Besov spaces to bounded Lipschitz domains, by intrinsic differences**: for
`1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f` agrees on `Ω` with some `F ∈ L_p(V)` with
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`. -/
theorem exists_besov_extension_iff_modulusOn (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (∃ F : Lp ℂ p (volume : Measure V), indicatorLp Ω.measurableSet F =
        indicatorLp Ω.measurableSet f ∧
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) < ∞) ↔
      modNormOn Ω.measurableSet r s q f < ∞ := by
  constructor
  · rintro ⟨F, hFf, hF⟩
    exact (modNormOn_le_modNorm_of_indicatorLp Ω.measurableSet r s q hFf).trans_lt hF
  · exact Ω.exists_besov_extension_of_modulusOn hp hs hsr hq

/-- **Restrictions of band-limited approximation spaces to bounded Lipschitz domains**: for
`1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f` agrees on `Ω` with some `F` in the approximation
space `A^s_q(L_p(V))` of band-limited functions iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`. -/
theorem exists_memApprox_extension_iff (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (∃ F : Lp ℂ p (volume : Measure V), indicatorLp Ω.measurableSet F =
        indicatorLp Ω.measurableSet f ∧ (bandScheme hp).MemApprox s q F) ↔
      modNormOn Ω.measurableSet r s q f < ∞ := by
  rw [← Ω.exists_besov_extension_iff_modulusOn hp hs hsr hq f]
  exact exists_congr fun F =>
    and_congr_right fun _ => memApprox_bandScheme_iff_modulus hp hs.le hsr hq F

end BoundedLipschitzDomain

end Rd
