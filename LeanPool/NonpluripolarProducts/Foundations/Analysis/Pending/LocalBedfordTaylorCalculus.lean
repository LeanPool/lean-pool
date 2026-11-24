/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing

/-!
# The algebra of bounded Bedford--Taylor products

On an open `U ⊆ ℂⁿ`, for the currents of `Pending.LocalProductCurrents` and the recursive product
`B(u₁, …, u_q; T)` of `Pending.LocalBedfordTaylorProducts` (`gnpp:bounded-calculus`,
`demailly-cadg:III.3.2`, `demailly-cadg:III.3.7`, `demailly-cadg:III.3.10`):

* `eq_of_local` — currents agreeing near every point are equal.
* `ddcWedge_comm` / `ddcMul_ddcMul_comm` — **two potentials commute**:
  `dd^c(a dd^c(b S)) = dd^c(b dd^c(a S))`, first for smooth potentials (2-forms commute), then for
  locally bounded PSH ones by decreasing continuity (`LocalBedfordTaylorDecreasing`).
* `btProduct_comp_perm` — **symmetry**: `B(u ∘ σ; T) = B(u; T)` for every permutation `σ`.
* `btProduct_update_add` — **additivity in each potential**.
* `btProduct_update_add_pluriharmonic` — adding a smooth pluriharmonic function (`dd^c h = 0`) in a
  slot does not change the product.
* `isPositive_btProduct_add_sub` / `traceMeasure_le_of_isPositive_sub` — **monotonicity**:
  `B(a + b; T) - B(a; T)` is positive for locally bounded PSH `a_i, b_i`; in top degree the
    measures
  satisfy `⋀ dd^c a_i ≤ ⋀ dd^c (a_i + b_i)`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  CoordinateWedgeAssoc ClosedProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorLocality LocalCurrentLebesgue ConstantFormProducts LocalBedfordTaylorForms
  LocalBedfordTaylorContinuity LocalBedfordTaylorCollar LocalBedfordTaylorMass
  LocalBedfordTaylorDecreasing

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U : Opens (ComplexModel n)}

/-! ### Locality -/

section Local

/-- **Currents agreeing near every point are equal.** -/
theorem eq_of_local {q : ℕ} {S S' : LocalProductCurrent n U q}
    (h : ∀ x ∈ (U : Set E), ∃ (V : Opens (ComplexModel n)) (hVU : V ≤ U), x ∈ V ∧
      restrict hVU S = restrict hVU S') : S = S' := by
  classical
  choose! V hVU hxV hV using h
  ext γ φ
  obtain ⟨s, ψ, hφ⟩ := exists_sum_extTest (fun i : (U : Set E) => V i) (fun i => hVU i i.2)
    (fun x hx => ⟨⟨x, hx⟩, hxV x hx⟩) φ
  rw [hφ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrArg (fun R => R γ (ψ i)) (hV i i.2)
  simpa only [LocalBedfordTaylorLocality.restrict_apply] using this

/-- A ball of half the radius of a ball in `U` is relatively compact in `U`. -/
theorem relativelyCompactIn_half_ball {x : E} {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ U) :
    RelativelyCompactIn (⟨ball x (r / 2), isOpen_ball⟩ : Opens (ComplexModel n)) U :=
  relativelyCompactIn_ball (by linarith) ((closedBall_subset_ball (by linarith)).trans hball)

end Local

/-! ### Two potentials commute -/

section Swap

/-- `(γ ∧ Q) ∧ P = (γ ∧ P) ∧ Q` for real `(1,1)`-forms `P, Q`. -/
theorem wedgeLM_comm {m : ℕ} {P Q : RealForm n 2} (hP : IsOneOne P) (hQ : IsOneOne Q)
    (γ : formSpan n m) :
    wedgeLM (m + 1) hP (wedgeLM m hQ γ) = wedgeLM (m + 1) hQ (wedgeLM m hP γ) := by
  ext1
  simp only [coe_wedgeLM_apply]
  have h := wedgeTo_wedgeTo_comm (k := 1) (γ : RealForm n (2 * m)) Q (oneOne_mem_formSpan hP)
    rfl rfl rfl rfl
  simpa only [wedgeTo_rfl] using h

theorem sum_sum_sum_sum_comm {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (f : ι → κ → ι → κ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **Smooth potentials commute**: `dd^c a ∧ (dd^c b ∧ S) = dd^c b ∧ (dd^c a ∧ S)` for every
current `S` and functions `a, b` smooth on `U`. -/
theorem ddcWedge_comm {m : ℕ} (S : LocalProductCurrent n U (m + 2)) {a b : E → ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ddcWedge (ddcWedge S hb) ha = ddcWedge (ddcWedge S ha) hb := by
  ext γ φ
  simp only [ddcWedge_apply, Finset.mul_sum]
  rw [sum_sum_sum_sum_comm (fun i j k l => -(1 / (4 * Real.pi)) * (-(1 / (4 * Real.pi)) *
    S (wedgeLM (m + 1) (isOneOne_coeffForm k l) (wedgeLM m (isOneOne_coeffForm i j) γ))
      (mulSmoothOnCLM (contDiffOn_hessFun ha k l)
        (mulSmoothOnCLM (contDiffOn_hessFun hb i j) φ))))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [wedgeLM_comm (isOneOne_coeffForm k l) (isOneOne_coeffForm i j)]
  congr 3
  ext x
  simp only [mulSmoothOnCLM_apply]
  ring

/-- `B(a, b; S) = dd^c(a dd^c(b S))`. -/
theorem btProduct_two {m : ℕ} (S : LocalProductCurrent n U (m + 2)) (a b : E → ℝ) :
    btProduct 2 m ![a, b] S = ddcMul (ddcMul S b) a := rfl

/-- **Two locally bounded PSH potentials commute**: `dd^c(a dd^c(b S)) = dd^c(b dd^c(a S))` for
`S` positive closed. This is the two-slot case of
[Demailly, Corollary III.3.10](https://www-fourier.univ-grenoble-alpes.fr/~demailly/source_files/analgeom/agbook.pdf#page=149). -/
theorem ddcMul_ddcMul_comm {m : ℕ} {S : LocalProductCurrent n U (m + 2)} (hS : IsPositive S)
    (hSc : IsClosedAny (m + 2) S) {a b : E → ℝ} (ha : IsLocallyBoundedPshOn U a)
    (hb : IsLocallyBoundedPshOn U b) : ddcMul (ddcMul S b) a = ddcMul (ddcMul S a) b := by
  refine eq_of_local fun x hx => ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel n) := ⟨ball x (r / 2), isOpen_ball⟩
  have hAU : A ≤ U := fun z hz => hball (ball_subset_ball (by linarith) hz)
  have hArel : RelativelyCompactIn A U := relativelyCompactIn_half_ball hr hball
  refine ⟨A, hAU, mem_ball_self (by linarith), ?_⟩
  obtain ⟨f, hf⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation ha hArel
  obtain ⟨g, hg⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hb hArel
  have hSA := isPositive_restrict hS hAU
  have hSAc := isClosedAny_restrict hSc hAU
  have haA := isLocallyBoundedPshOn_mono ha hAU
  have hbA := isLocallyBoundedPshOn_mono hb hAU
  have hfA : ∀ k, IsLocallyBoundedPshOn A (f k) := fun k =>
    isLocallyBoundedPshOn_of_isSmoothPshOn (hf.1 k)
  have hgA : ∀ k, IsLocallyBoundedPshOn A (g k) := fun k =>
    isLocallyBoundedPshOn_of_isSmoothPshOn (hg.1 k)
  have e : ∀ (c d : E → ℝ), IsLocallyBoundedPshOn U c → IsLocallyBoundedPshOn U d →
      restrict hAU (ddcMul (ddcMul S d) c) = btProduct 2 m ![c, d] (restrict hAU S) := by
    intro c d hc hd
    rw [btProduct_two, ddcMul_restrict hS hAU hd,
      ddcMul_restrict (isPositive_ddcMul hS hSc hd).1 hAU hc]
  rw [e a b ha hb, e b a hb ha]
  -- the smooth approximations commute
  have hsm : ∀ k, btProduct 2 m ![f k, g k] (restrict hAU S) =
      btProduct 2 m ![g k, f k] (restrict hAU S) := by
    intro k
    have h1 := isPositive_ddcMul hSA hSAc (hgA k)
    have h2 := isPositive_ddcMul hSA hSAc (hfA k)
    rw [btProduct_two, btProduct_two, ddcMul_eq_ddcWedge h1.1 h1.2 (hf.1 k).1,
      ddcMul_eq_ddcWedge h2.1 h2.2 (hg.1 k).1, ddcMul_eq_ddcWedge hSA hSAc (hg.1 k).1,
      ddcMul_eq_ddcWedge hSA hSAc (hf.1 k).1]
    exact ddcWedge_comm _ (hf.1 k).1 (hg.1 k).1
  have hPSH : ∀ (c d : ℕ → E → ℝ), (∀ k, IsLocallyBoundedPshOn A (c k)) →
      (∀ k, IsLocallyBoundedPshOn A (d k)) → ∀ k i, IsLocallyBoundedPshOn A (![c k, d k] i) := by
    intro c d hc hd k i
    fin_cases i
    · exact hc k
    · exact hd k
  have hPSH₀ : ∀ (c d : E → ℝ), IsLocallyBoundedPshOn A c → IsLocallyBoundedPshOn A d →
      ∀ i, IsLocallyBoundedPshOn A (![c, d] i) := by
    intro c d hc hd i
    fin_cases i
    · exact hc
    · exact hd
  have hanti : ∀ (c d : ℕ → E → ℝ), (∀ z ∈ (A : Set E), Antitone fun k => c k z) →
      (∀ z ∈ (A : Set E), Antitone fun k => d k z) →
      ∀ i, ∀ z ∈ (A : Set E), Antitone fun k => ![c k, d k] i z := by
    intro c d hc hd i z hz
    fin_cases i
    · exact hc z hz
    · exact hd z hz
  have hlim : ∀ (c d : ℕ → E → ℝ) (c₀ d₀ : E → ℝ),
      (∀ z ∈ (A : Set E), Tendsto (fun k => c k z) atTop (𝓝 (c₀ z))) →
      (∀ z ∈ (A : Set E), Tendsto (fun k => d k z) atTop (𝓝 (d₀ z))) →
      ∀ i, ∀ z ∈ (A : Set E), Tendsto (fun k => ![c k, d k] i z) atTop (𝓝 (![c₀, d₀] i z)) := by
    intro c d c₀ d₀ hc hd i z hz
    fin_cases i
    · exact hc z hz
    · exact hd z hz
  have hL := weakTendsto_btProduct_of_antitone 2 m (restrict hAU S) hSA hSAc
    (fun k => ![f k, g k]) ![a, b] (hPSH f g hfA hgA) (hPSH₀ a b haA hbA)
    (hanti f g hf.2.1 hg.2.1) (hlim f g a b hf.2.2 hg.2.2)
  have hR := weakTendsto_btProduct_of_antitone 2 m (restrict hAU S) hSA hSAc
    (fun k => ![g k, f k]) ![b, a] (hPSH g f hgA hfA) (hPSH₀ b a hbA haA)
    (hanti g f hg.2.1 hf.2.1) (hlim g f b a hg.2.2 hf.2.2)
  ext γ φ
  refine tendsto_nhds_unique (hL γ φ) ?_
  simpa only [hsm] using hR γ φ

end Swap

/-! ### Symmetry -/

section Symmetry

/-- **The two outermost potentials commute.** -/
theorem btProduct_comp_swap_zero_one (q r : ℕ) (T : LocalProductCurrent n U (r + (q + 2)))
    (hT : IsPositive T) (hTc : IsClosedAny (r + (q + 2)) T) (v : Fin (q + 2) → E → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i)) :
    btProduct (q + 2) r (v ∘ Equiv.swap 0 1) T = btProduct (q + 2) r v T := by
  have h1 : r + (q + 2) = r + 1 + (q + 1) := by omega
  have h2 : r + 1 + (q + 1) = r + 1 + 1 + q := by omega
  have hT' := isPositive_castLPC h1 hT
  have hT'c := isClosedAny_castLPC h1 hTc
  have hT'' := isPositive_castLPC h2 hT'
  have hT''c := isClosedAny_castLPC h2 hT'c
  have peel : ∀ w : Fin (q + 2) → E → ℝ, btProduct (q + 2) r w T =
      ddcMul (ddcMul (btProduct q (r + 1 + 1) (Fin.tail (Fin.tail w)) (castLPC h2 (castLPC h1 T)))
        (Fin.tail w 0)) (w 0) := by
    intro w
    rw [btProduct_succ_eq_ddcMul (q + 1) r w T (castLPC h1 T) (heq_castLPC h1 T),
      btProduct_succ_eq_ddcMul q (r + 1) (Fin.tail w) (castLPC h1 T) _
        (heq_castLPC h2 (castLPC h1 T))]
  have hX := isPositive_btProduct q (r + 1 + 1) (Fin.tail (Fin.tail v))
    (castLPC h2 (castLPC h1 T)) hT'' hT''c fun i => hv _
  have et : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
  rw [peel, peel, et]
  simp only [Fin.tail, Function.comp_apply, Fin.succ_zero_eq_one', Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  exact ddcMul_ddcMul_comm (m := r) hX.1 hX.2 (hv 1) (hv 0)

/-- Swapping two potentials other than the outermost one. -/
theorem btProduct_comp_swap_succ (q r : ℕ)
    (IH : ∀ (r : ℕ) (T : LocalProductCurrent n U (r + q)), IsPositive T → IsClosedAny (r + q) T →
      ∀ (u : Fin q → E → ℝ), (∀ i, IsLocallyBoundedPshOn U (u i)) →
      ∀ σ : Equiv.Perm (Fin q), btProduct q r (u ∘ σ) T = btProduct q r u T)
    (T : LocalProductCurrent n U (r + (q + 1))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (q + 1)) T) (v : Fin (q + 1) → E → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i)) (x y : Fin q) :
    btProduct (q + 1) r (v ∘ Equiv.swap x.succ y.succ) T = btProduct (q + 1) r v T := by
  have h1 : r + (q + 1) = r + 1 + q := by omega
  rw [btProduct_succ_eq_ddcMul q r _ T (castLPC h1 T) (heq_castLPC h1 T),
    btProduct_succ_eq_ddcMul q r v T (castLPC h1 T) (heq_castLPC h1 T)]
  have e0 : (v ∘ Equiv.swap x.succ y.succ) 0 = v 0 := by
    simp only [Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero x).symm (Fin.succ_ne_zero y).symm]
  have et : Fin.tail (v ∘ Equiv.swap x.succ y.succ) = Fin.tail v ∘ Equiv.swap x y := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [(Fin.succ_injective q).swap_apply]
  rw [e0, et, IH (r + 1) (castLPC h1 T) (isPositive_castLPC h1 hT) (isClosedAny_castLPC h1 hTc)
    (Fin.tail v) (fun i => hv _) (Equiv.swap x y)]

/-- **Symmetry of the recursive product** ([Demailly, Corollary III.3.10](https://www-fourier.univ-grenoble-alpes.fr/~demailly/source_files/analgeom/agbook.pdf#page=149)).
`B(u_{σ(1)}, …, u_{σ(q)}; T) = B(u_1, …, u_q; T)` for every permutation `σ`, `T` positive closed
    and
`u_i` locally bounded PSH. -/
theorem btProduct_comp_perm : ∀ (q r : ℕ) (T : LocalProductCurrent n U (r + q)), IsPositive T →
    IsClosedAny (r + q) T → ∀ (u : Fin q → E → ℝ), (∀ i, IsLocallyBoundedPshOn U (u i)) →
    ∀ σ : Equiv.Perm (Fin q), btProduct q r (u ∘ σ) T = btProduct q r u T
  | 0, _, _, _, _, u, _, _ => by
    congr 1
    funext i
    exact i.elim0
  | q + 1, r, T, hT, hTc, u, hu, σ => by
    have hsucc : ∀ (x' y' : Fin q) (w : Fin (q + 1) → E → ℝ),
        (∀ i, IsLocallyBoundedPshOn U (w i)) →
        btProduct (q + 1) r (w ∘ Equiv.swap x'.succ y'.succ) T = btProduct (q + 1) r w T :=
      fun x' y' w hw => btProduct_comp_swap_succ q r (btProduct_comp_perm q) T hT hTc w hw x' y'
    have hswap0 : ∀ (y : Fin (q + 1)) (w : Fin (q + 1) → E → ℝ),
        (∀ i, IsLocallyBoundedPshOn U (w i)) →
        btProduct (q + 1) r (w ∘ Equiv.swap 0 y) T = btProduct (q + 1) r w T := by
      intro y w hw
      rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y', rfl⟩
      · rw [Equiv.swap_self, Equiv.coe_refl, Function.comp_id]
      cases q with
      | zero => exact y'.elim0
      | succ q' =>
        rcases Fin.eq_zero_or_eq_succ y' with rfl | ⟨y'', rfl⟩
        · rw [Fin.succ_zero_eq_one']
          exact btProduct_comp_swap_zero_one q' r T hT hTc w hw
        · have hne1 : (0 : Fin (q' + 2)) ≠ 1 := by simp
          have hne2 : (0 : Fin (q' + 2)) ≠ y''.succ.succ := (Fin.succ_ne_zero _).symm
          have hdec : Equiv.swap (0 : Fin (q' + 2)) y''.succ.succ =
              Equiv.swap 1 y''.succ.succ * Equiv.swap 0 1 * Equiv.swap 1 y''.succ.succ := by
            rw [Equiv.swap_mul_swap_mul_swap hne1 hne2, Equiv.swap_comm]
          have hw1 : ∀ i, IsLocallyBoundedPshOn U ((w ∘ Equiv.swap 1 y''.succ.succ) i) :=
            fun i => hw _
          have hw2 : ∀ i, IsLocallyBoundedPshOn U
              (((w ∘ Equiv.swap 1 y''.succ.succ) ∘ Equiv.swap 0 1) i) := fun i => hw _
          have e1 : Equiv.swap (1 : Fin (q' + 2)) y''.succ.succ =
              Equiv.swap (0 : Fin (q' + 1)).succ y''.succ.succ := by
            rw [Fin.succ_zero_eq_one']
          rw [hdec, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← Function.comp_assoc,
            ← Function.comp_assoc, e1, hsucc 0 y''.succ _ (by rw [← e1]; exact hw2), ← e1,
            btProduct_comp_swap_zero_one q' r T hT hTc _ hw1, e1, hsucc 0 y''.succ w hw]
    have hswap : ∀ (x y : Fin (q + 1)) (w : Fin (q + 1) → E → ℝ),
        (∀ i, IsLocallyBoundedPshOn U (w i)) →
        btProduct (q + 1) r (w ∘ Equiv.swap x y) T = btProduct (q + 1) r w T := by
      intro x y w hw
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x', rfl⟩
      · exact hswap0 y w hw
      rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y', rfl⟩
      · rw [Equiv.swap_comm]
        exact hswap0 _ w hw
      · exact hsucc x' y' w hw
    refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ w : Fin (q + 1) → E → ℝ,
      (∀ i, IsLocallyBoundedPshOn U (w i)) → btProduct (q + 1) r (w ∘ σ) T =
        btProduct (q + 1) r w T) σ ?_ ?_ u hu
    · intro w _
      rw [Equiv.Perm.coe_one, Function.comp_id]
    · intro f x y _ ih w hw
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ih (w ∘ Equiv.swap x y) (fun i => hw _),
        hswap x y w hw]

end Symmetry

/-! ### Additivity, pluriharmonic invariance and monotonicity -/

section Additivity

theorem isLocallyBoundedPshOn_add {a a' : E → ℝ} (ha : IsLocallyBoundedPshOn U a)
    (ha' : IsLocallyBoundedPshOn U a') : IsLocallyBoundedPshOn U fun z => a z + a' z := by
  refine ⟨?_, fun z hz => ?_⟩
  · simpa only [EReal.coe_add] using ha.1.add ha'.1
  · obtain ⟨V, hzV, hVU, C, hC⟩ := ha.2 z hz
    obtain ⟨V', hzV', -, C', hC'⟩ := ha'.2 z hz
    exact ⟨V ⊓ V', ⟨hzV, hzV'⟩, inf_le_left.trans hVU, C + C', fun y hy =>
      (abs_add_le _ _).trans (add_le_add (hC y hy.1) (hC' y hy.2))⟩

theorem isLocallyBoundedPshOn_of_continuousOn {g : E → ℝ}
    (hp : PlurisubharmonicOn (fun z => (g z : EReal)) U) (hc : ContinuousOn g U) :
    IsLocallyBoundedPshOn U g := by
  refine ⟨hp, fun z hz => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen z hz
  have hcb : closedBall z (r / 2) ⊆ (U : Set E) := (closedBall_subset_ball (by linarith)).trans
    hball
  obtain ⟨C, hC⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn (hc.mono hcb)
  exact ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
    fun w hw => hcb (ball_subset_closedBall hw), C, fun w hw => by
      simpa [Real.norm_eq_abs] using hC w (ball_subset_closedBall hw)⟩

/-- `dd^c((a + a') S) = dd^c(a S) + dd^c(a' S)`. -/
theorem ddcMul_add {m : ℕ} {S : LocalProductCurrent n U (m + 1)} (hS : IsPositive S)
    {a a' : E → ℝ} (ha : Measurable ((U : Set E).indicator a))
    (hab : IsLocallyBoundedOn ((U : Set E).indicator a) U)
    (ha' : Measurable ((U : Set E).indicator a'))
    (ha'b : IsLocallyBoundedOn ((U : Set E).indicator a') U) :
    ddcMul S (fun z => a z + a' z) = ddcMul S a + ddcMul S a' := by
  have e : (U : Set E).indicator (fun z => a z + a' z) =
      (U : Set E).indicator a + (U : Set E).indicator a' := by
    funext z
    by_cases hz : z ∈ (U : Set E) <;> simp [hz]
  rw [ddcMul, ddcMul, ddcMul, e, mulBorel_add hS ha hab ha' ha'b, ddc_add]

/-- Moving the potential of slot `j` to the outermost slot. -/
theorem btProduct_update_eq (q r : ℕ) (T : LocalProductCurrent n U (r + (q + 1)))
    (hT : IsPositive T) (hTc : IsClosedAny (r + (q + 1)) T) (u : Fin (q + 1) → E → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (j : Fin (q + 1)) {c : E → ℝ}
    (hc : IsLocallyBoundedPshOn U c) :
    btProduct (q + 1) r (Function.update u j c) T =
      btProduct (q + 1) r (Function.update (u ∘ Equiv.swap 0 j) 0 c) T := by
  classical
  have hP : ∀ i, IsLocallyBoundedPshOn U (Function.update u j c i) := fun i => by
    by_cases hi : i = j
    · subst hi
      simpa using hc
    · simpa [hi] using hu i
  rw [← btProduct_comp_perm (q + 1) r T hT hTc _ hP (Equiv.swap 0 j),
    Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]

/-- **Additivity in the outermost potential.** -/
theorem btProduct_update_zero_add (q r : ℕ) (T : LocalProductCurrent n U (r + (q + 1)))
    (hT : IsPositive T) (hTc : IsClosedAny (r + (q + 1)) T) (u : Fin (q + 1) → E → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) {a a' : E → ℝ}
    (ha : Measurable ((U : Set E).indicator a))
    (hab : IsLocallyBoundedOn ((U : Set E).indicator a) U)
    (ha' : Measurable ((U : Set E).indicator a'))
    (ha'b : IsLocallyBoundedOn ((U : Set E).indicator a') U) :
    btProduct (q + 1) r (Function.update u 0 fun z => a z + a' z) T =
      btProduct (q + 1) r (Function.update u 0 a) T +
        btProduct (q + 1) r (Function.update u 0 a') T := by
  have h1 : r + (q + 1) = r + 1 + q := by omega
  have hX := isPositive_btProduct q (r + 1) (Fin.tail u) (castLPC h1 T)
    (isPositive_castLPC h1 hT) (isClosedAny_castLPC h1 hTc) fun i => hu _
  simp only [btProduct_succ_eq_ddcMul q r _ T (castLPC h1 T) (heq_castLPC h1 T),
    Fin.tail_update_zero, Function.update_self]
  exact ddcMul_add hX.1 ha hab ha' ha'b

/-- **Additivity in each potential** (`gnpp:bounded-calculus`). -/
theorem btProduct_update_add (q r : ℕ) (T : LocalProductCurrent n U (r + q)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + q) T) (u : Fin q → E → ℝ) (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
    (j : Fin q) {a a' : E → ℝ} (ha : IsLocallyBoundedPshOn U a)
    (ha' : IsLocallyBoundedPshOn U a') :
    btProduct q r (Function.update u j fun z => a z + a' z) T =
      btProduct q r (Function.update u j a) T + btProduct q r (Function.update u j a') T := by
  cases q with
  | zero => exact j.elim0
  | succ q =>
    rw [btProduct_update_eq q r T hT hTc u hu j (isLocallyBoundedPshOn_add ha ha'),
      btProduct_update_eq q r T hT hTc u hu j ha, btProduct_update_eq q r T hT hTc u hu j ha']
    exact btProduct_update_zero_add q r T hT hTc _ (fun i => hu _)
      (measurable_indicator_of_isLocallyBoundedPshOn ha) (isLocallyBoundedOn_indicator ha)
      (measurable_indicator_of_isLocallyBoundedPshOn ha') (isLocallyBoundedOn_indicator ha')

/-- `dd^c(h S) = 0` for `h` smooth with `dd^c h = 0` on `U`. -/
theorem ddcMul_eq_zero_of_smoothDDC_eq_zero {m : ℕ} {S : LocalProductCurrent n U (m + 1)}
    (hS : IsPositive S) (hSc : IsClosedCurrent S) {h : E → ℝ} (hh : ContDiffOn ℝ ∞ h U)
    (h0 : ∀ z ∈ (U : Set E), smoothDDC h z = 0) : ddcMul S h = 0 := by
  rw [ddcMul_eq_ddcWedge hS hSc hh, ddcWedge_eq_wedgeForm]
  ext γ φ
  rw [wedgeForm_apply_eq rfl S (contDiffOn_ddcForm hh)
    (fun x hx => by rw [ddcForm, h0 x hx]; exact Submodule.zero_mem _) (κ := Empty)
    (fun _ => fun _ => 0) (fun _ => contDiffOn_const) (fun e => e.elim)
    (fun x hx => by rw [ddcForm, h0 x hx]; simp) γ φ]
  simp

/-- **A Bedford–Taylor product with a smooth pluriharmonic factor vanishes**:
`B(u₁, …, h, …, u_p; T) = 0` when `h` is smooth on `U` with `dd^c h = 0` and `T` is closed and
positive. -/
theorem btProduct_update_eq_zero_of_pluriharmonic (p q : ℕ) (T : LocalProductCurrent n U (q + p))
    (hT : IsPositive T) (hTc : IsClosedAny (q + p) T) (u : Fin p → E → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (j : Fin p) {h : E → ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ z ∈ (U : Set E), smoothDDC h z = 0) :
    btProduct p q (Function.update u j h) T = 0 := by
  have hhp : IsLocallyBoundedPshOn U h := isLocallyBoundedPshOn_of_continuousOn
    (plurisubharmonicOn_coe_of_smoothDDC_eq_zero U.isOpen hh h0) hh.continuousOn
  cases p with
  | zero => exact j.elim0
  | succ p =>
    have h1 : q + (p + 1) = q + 1 + p := by omega
    have hX := isPositive_btProduct p (q + 1) (Fin.tail (u ∘ Equiv.swap 0 j)) (castLPC h1 T)
      (isPositive_castLPC h1 hT) (isClosedAny_castLPC h1 hTc) fun i => hu _
    rw [btProduct_update_eq p q T hT hTc u hu j hhp,
      btProduct_succ_eq_ddcMul p q (Function.update (u ∘ Equiv.swap 0 j) 0 h) T (castLPC h1 T)
        (heq_castLPC h1 T), Fin.tail_update_zero, Function.update_self,
      ddcMul_eq_zero_of_smoothDDC_eq_zero hX.1 hX.2 hh h0]

/-- **Adding a smooth pluriharmonic function (`dd^c h = 0`) in a slot does not change the
product** (`gnpp:bounded-calculus`). -/
theorem btProduct_update_add_pluriharmonic (q r : ℕ) (T : LocalProductCurrent n U (r + q))
    (hT : IsPositive T) (hTc : IsClosedAny (r + q) T) (u : Fin q → E → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (j : Fin q) {h : E → ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ z ∈ (U : Set E), smoothDDC h z = 0) :
    btProduct q r (Function.update u j fun z => u j z + h z) T = btProduct q r u T := by
  have hhp : IsLocallyBoundedPshOn U h := isLocallyBoundedPshOn_of_continuousOn
    (plurisubharmonicOn_coe_of_smoothDDC_eq_zero U.isOpen hh h0) hh.continuousOn
  rw [btProduct_update_add q r T hT hTc u hu j (hu j) hhp, Function.update_eq_self]
  rw [btProduct_update_eq_zero_of_pluriharmonic q r T hT hTc u hu j hh h0, add_zero]

/-- **Monotonicity**: `B(a_1 + b_1, …, a_q + b_q; T) - B(a_1, …, a_q; T)` is positive for locally
bounded PSH `a_i, b_i` (expand by additivity; the other terms are positive products). -/
theorem isPositive_btProduct_add_sub (q r : ℕ) (T : LocalProductCurrent n U (r + q))
    (hT : IsPositive T) (hTc : IsClosedAny (r + q) T) (a b : Fin q → E → ℝ)
    (ha : ∀ i, IsLocallyBoundedPshOn U (a i)) (hb : ∀ i, IsLocallyBoundedPshOn U (b i)) :
    IsPositive (btProduct q r (fun i z => a i z + b i z) T - btProduct q r a T) := by
  classical
  set c : ℕ → Fin q → E → ℝ := fun j i => if (i : ℕ) < j then fun z => a i z + b i z else a i
    with hc_def
  have hcP : ∀ j i, IsLocallyBoundedPshOn U (c j i) := fun j i => by
    simp only [hc_def]
    split_ifs
    · exact isLocallyBoundedPshOn_add (ha i) (hb i)
    · exact ha i
  have key : ∀ j, j ≤ q → IsPositive (btProduct q r (c j) T - btProduct q r a T) := by
    intro j
    induction j with
    | zero =>
      intro _
      have e : c 0 = a := by
        funext i
        simp [hc_def]
      rw [e, sub_self]
      exact isPositive_zero
    | succ j ih =>
      intro hj
      set jj : Fin q := ⟨j, by omega⟩
      have e1 : c (j + 1) = Function.update (c j) jj fun z => a jj z + b jj z := by
        funext i
        by_cases hi : i = jj
        · subst hi
          simp [hc_def, jj]
        · have hi' : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi]
          simp only [hc_def]
          by_cases hlt : (i : ℕ) < j
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have : ¬ (i : ℕ) < j + 1 := by omega
            simp [hlt, this]
      have e2 : Function.update (c j) jj (a jj) = c j := by
        rw [Function.update_eq_iff]
        refine ⟨by simp [hc_def, jj], fun _ _ => rfl⟩
      have hadd := btProduct_update_add q r T hT hTc (c j) (hcP j) jj (ha jj) (hb jj)
      rw [e2] at hadd
      have e3 : btProduct q r (c (j + 1)) T - btProduct q r a T =
          (btProduct q r (c j) T - btProduct q r a T) +
            btProduct q r (Function.update (c j) jj (b jj)) T := by
        rw [e1, hadd]
        abel
      rw [e3]
      refine (ih (by omega)).add (isPositive_btProduct q r _ T hT hTc fun i => ?_).1
      by_cases hi : i = jj
      · subst hi
        simpa using hb jj
      · simpa [hi] using hcP j i
  have e : c q = fun i z => a i z + b i z := by
    funext i
    simp [hc_def, i.2]
  simpa [e] using key q le_rfl

/-- **Monotonicity of trace measures**: if `R - L` is positive, then `σ_L ≤ σ_R`. In top degree
this is the inequality `⋀ dd^c a_i ≤ ⋀ dd^c (a_i + b_i)` of `gnpp:bounded-calculus`. -/
theorem traceMeasure_le_of_isPositive_sub {m : ℕ} {L R : LocalProductCurrent n U m}
    (hL : IsPositive L) (hR : IsPositive R) (h : IsPositive (R - L)) :
    hL.traceMeasure ≤ hR.traceMeasure := by
  have hint : ∀ {S : LocalProductCurrent n U m} (hS : IsPositive S) (φ : 𝓓(U, ℝ)),
      Integrable (fun x => φ x) hS.traceMeasure := by
    intro S hS φ
    obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
    exact integrable_of_bounded_of_vanishing (hS.traceMeasure_lt_top φ.hasCompactSupport
      φ.tsupport_subset) φ.continuous.measurable (M := C)
      (fun x => by simpa [Real.norm_eq_abs] using hC x)
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have hsum : hR.traceMeasure = hL.traceMeasure + h.traceMeasure := by
    apply eq_of_forall_testFunction_integral_eq (U := U)
    · exact hR.traceMeasure_compl
    · rw [add_apply, hL.traceMeasure_compl, h.traceMeasure_compl, add_zero]
    · exact fun K hK hKU => hR.traceMeasure_lt_top hK hKU
    · intro K hK hKU
      rw [add_apply]
      exact ENNReal.add_lt_top.mpr ⟨hL.traceMeasure_lt_top hK hKU, h.traceMeasure_lt_top hK hKU⟩
    · intro φ
      rw [integral_add_measure (hint hL φ) (hint h φ), hR.integral_traceMeasure,
        hL.integral_traceMeasure, h.integral_traceMeasure, LinearMap.sub_apply, _root_.sub_apply]
      ring
  rw [hsum]
  exact Measure.le_add_right le_rfl

/-- **The top-degree inequality** `⋀ dd^c a_i ≤ ⋀ dd^c (a_i + b_i)` of the measures
`B(·; [1])`, for locally bounded PSH `a_i` and `b_i` (in particular smooth PSH `b_i`). -/
theorem traceMeasure_btProduct_le_add (a b : Fin n → E → ℝ)
    (ha : ∀ i, IsLocallyBoundedPshOn U (a i)) (hb : ∀ i, IsLocallyBoundedPshOn U (b i))
    (hL : IsPositive (btProduct n 0 a (oneCurrentOf (U := U) (Nat.zero_add n))))
    (hR : IsPositive (btProduct n 0 (fun i z => a i z + b i z)
      (oneCurrentOf (U := U) (Nat.zero_add n)))) :
    hL.traceMeasure ≤ hR.traceMeasure :=
  traceMeasure_le_of_isPositive_sub hL hR (isPositive_btProduct_add_sub n 0 _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) a b ha hb)

end Additivity

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
