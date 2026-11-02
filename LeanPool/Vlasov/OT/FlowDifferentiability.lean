/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.OT.FrozenField
public import LeanPool.Vlasov.ForMathlib.VariationalEquation
import all LeanPool.Vlasov.ForMathlib.VariationalEquation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Differentiability and inversion of the frozen Vlasov flow

The variational equation gives the spatial and joint derivatives of the flow and
its inverse. The Jacobian and explicit fundamental matrix remain together so
their generated proof declarations are shared as before.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory

variable {d : ℕ} [NeZero d]

/-- **C3 D1 (Jacobian).**  The phase-space Jacobian `A(s, p) = D_w b(s, p)` of the frozen Vlasov
field at the base point `p`: the block continuous-linear map `δ ↦ (δ.2, −(D_x conv ρ_s)(p.1)·δ.1)`,
where `D_x conv ρ_s (p.1) = ∫ y, fderiv ℝ gradW (p.1 − y) ∂ρ_s` (F1).  This is the coefficient of
the linear variational ODE `M' = A(s, Φ_s z)·M`; `vlasovVectorField_hasFDerivAt_in_z` (F2) says it
is the Fréchet derivative of `vlasovVectorField gradW ρ s` at `p.2`. -/
noncomputable def vlasovFieldJacobian (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d)) (p : ℝ × PhaseSpace d) : PhaseSpace d →L[ℝ] PhaseSpace d :=
  (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
    (-((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))

omit [NeZero d] in
/-- Joint continuity of the Jacobian on `Icc 0 T ×ˢ univ`.
Express the block map as a sum of continuous compositions of the convolution derivative. -/
lemma vlasovFieldJacobian_continuousOn
    (gradW : PhysSpace d → PhysSpace d) (ρ : ℝ → Measure (PhysSpace d)) (T : ℝ)
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ContinuousOn (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) := by
  have hg_cont : Continuous (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hD2 : ContinuousOn
      (fun p : ℝ × PhaseSpace d => ∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ Set.univ) :=
    hρD_cont.comp hg_cont.continuousOn hmaps
  have hDcomp : ContinuousOn
      (fun p : ℝ × PhaseSpace d => -((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) (Set.Icc 0 T ×ˢ Set.univ) :=
    (hD2.clm_comp continuousOn_const).neg
  have heq : (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p) = fun p =>
        (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)).comp
          (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d))
        + (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)).comp
          (-((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
              (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) := by
    funext p; ext x <;> simp [vlasovFieldJacobian]
  rw [heq]; exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)

omit [NeZero d] in
/-- **C3 D1a — the uniform-over-compact first-order Taylor remainder of the Vlasov field.**

For a fixed initial point `z`, the first-order remainder of the frozen field `b(s,·)` at the moving
base point `Φ_s z := (charX s z, charV s z)`,
`R(s,w) = b(s,w) − b(s,Φ_s z) − A(s,Φ_s z)·(w − Φ_s z)`, is `o(‖w − Φ_s z‖)` **uniformly in
`s ∈ [0,T]`**: for every `η > 0` there is a single `δ > 0` (independent of `s`) with
`‖R(s,w)‖ ≤ η·‖w − Φ_s z‖` whenever `‖w − Φ_s z‖ ≤ δ`.

This uniformity is the load-bearing analytic core of D1 (the variational-equation difference
quotient): it is what lets Grönwall bound `Φ_t(z+h) − Φ_t(z) − M_t(z)·h` by `o(‖h‖)` *uniformly
along the trajectory*.  Proof: the flow image `{Φ_s z : s ∈ [0,T]}` is compact (continuous image of
`[0,T]`), `A = D_w b` is jointly `(s,w)`-continuous (from `hρD_cont`), so `A` is **uniformly**
continuous on the compact tube `Γ = {(s, Φ_s z + e) : s ∈ [0,T], ‖e‖ ≤ 1}` (Heine–Cantor); the
mean-value inequality on `closedBall (Φ_s z) δ` then converts the modulus into the remainder
bound. -/
lemma vlasovField_taylorRemainder_uniform
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (z : PhaseSpace d)
    (hcontIcc : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ w : PhaseSpace d,
      ‖w - (charX s z, charV s z)‖ ≤ δ →
      ‖vlasovVectorField gradW ρ s w - vlasovVectorField gradW ρ s (charX s z, charV s z)
        - (vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z))) (w - (charX s z, charV s z))‖
        ≤ η * ‖w - (charX s z, charV s z)‖ := by
  set Φ : ℝ → PhaseSpace d := fun s => (charX s z, charV s z) with hΦ
  -- F2: the field is differentiable in the phase variable with derivative `vlasovFieldJacobian`.
  have hF2 : ∀ s (w : PhaseSpace d),
      HasFDerivAt (vlasovVectorField gradW ρ s) (vlasovFieldJacobian gradW ρ (s, w)) w :=
    fun s w => vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s w
  -- Joint continuity of the Jacobian on `Icc 0 T ×ˢ Set.univ` (from `hρD_cont`).
  have hg_cont : Continuous (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hD2 : ContinuousOn
      (fun p : ℝ × PhaseSpace d => ∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ Set.univ) :=
    hρD_cont.comp hg_cont.continuousOn hmaps
  have hDcomp : ContinuousOn
      (fun p : ℝ × PhaseSpace d => -((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) (Set.Icc 0 T ×ˢ Set.univ) :=
    (hD2.clm_comp continuousOn_const).neg
  have heq : (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p) = fun p =>
        (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)).comp
          (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d))
        + (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)).comp
          (-((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
              (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) := by
    funext p; ext x <;> simp [vlasovFieldJacobian]
  have hAj_cont : ContinuousOn (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p)
      (Set.Icc 0 T ×ˢ Set.univ) := by
    rw [heq]; exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)
  -- The compact tube `Γ = {(s, Φ s + e) : s ∈ [0,T], ‖e‖ ≤ 1}`.
  set ball1 : Set (PhaseSpace d) := Metric.closedBall 0 1 with hball1
  have hmap : ContinuousOn (fun q : ℝ × PhaseSpace d => ((q.1, Φ q.1 + q.2) : ℝ × PhaseSpace d))
      (Set.Icc 0 T ×ˢ ball1) :=
    continuousOn_fst.prodMk
      ((hcontIcc.comp continuousOn_fst (fun q hq => hq.1)).add continuousOn_snd)
  set Γ : Set (ℝ × PhaseSpace d) :=
    (fun q : ℝ × PhaseSpace d => ((q.1, Φ q.1 + q.2) : ℝ × PhaseSpace d)) '' (Set.Icc 0 T ×ˢ ball1)
    with hΓ
  have hΓcompact : IsCompact Γ :=
    (isCompact_Icc.prod (isCompact_closedBall 0 1)).image_of_continuousOn hmap
  have hΓsub : Γ ⊆ Set.Icc 0 T ×ˢ Set.univ := by
    rintro _ ⟨q, hq, rfl⟩; exact ⟨hq.1, Set.mem_univ _⟩
  have hUC : UniformContinuousOn (fun p => vlasovFieldJacobian gradW ρ p) Γ :=
    hΓcompact.uniformContinuousOn_of_continuous (hAj_cont.mono hΓsub)
  have hmemΓ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e : PhaseSpace d, ‖e‖ ≤ 1 →
      ((s, Φ s + e) : ℝ × PhaseSpace d) ∈ Γ := by
    intro s hs e he
    exact ⟨(s, e), ⟨hs, by simpa [hball1, Metric.mem_closedBall, dist_eq_norm] using he⟩, rfl⟩
  -- Extract the uniform-continuity modulus.
  intro η hη
  obtain ⟨δ₀, hδ₀, H⟩ := Metric.uniformContinuousOn_iff_le.mp hUC η hη
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, ?_⟩
  intro s hs w hw
  -- Mean value on the convex ball `C = closedBall (Φ s) (min δ₀ 1)`.
  set C : Set (PhaseSpace d) := Metric.closedBall (Φ s) (min δ₀ 1) with hC
  have hΦmem : Φ s ∈ C := Metric.mem_closedBall_self (le_min hδ₀.le zero_le_one)
  have hwmem : w ∈ C := by
    rw [hC, Metric.mem_closedBall, dist_eq_norm]; exact hw
  -- The fderiv bound on `C` from uniform continuity.
  have hbound : ∀ w' ∈ C,
      ‖vlasovFieldJacobian gradW ρ (s, w') - vlasovFieldJacobian gradW ρ (s, Φ s)‖ ≤ η := by
    intro w' hw'
    have hw'norm : ‖w' - Φ s‖ ≤ min δ₀ 1 := by
      rw [← dist_eq_norm]; rw [hC, Metric.mem_closedBall] at hw'; exact hw'
    have hw'le1 : ‖w' - Φ s‖ ≤ 1 := hw'norm.trans (min_le_right _ _)
    have hmem1 : ((s, w') : ℝ × PhaseSpace d) ∈ Γ := by
      have := hmemΓ s hs (w' - Φ s) hw'le1
      rwa [add_sub_cancel] at this
    have hmem2 : ((s, Φ s) : ℝ × PhaseSpace d) ∈ Γ := by
      have := hmemΓ s hs 0 (by simp)
      rwa [add_zero] at this
    have hdist : dist ((s, w') : ℝ × PhaseSpace d) (s, Φ s) ≤ δ₀ := by
      rw [Prod.dist_eq]
      simp only [dist_self, max_le_iff]
      refine ⟨hδ₀.le, ?_⟩
      rw [dist_eq_norm]; exact hw'norm.trans (min_le_left _ _)
    have := H _ hmem1 _ hmem2 hdist
    rwa [dist_eq_norm] at this
  -- Apply the mean value inequality to `g u = b(s,u) − A(s,Φ s)·u`.
  have hg : ∀ w' ∈ C, HasFDerivWithinAt
      (fun u => vlasovVectorField gradW ρ s u - vlasovFieldJacobian gradW ρ (s, Φ s) u)
      (vlasovFieldJacobian gradW ρ (s, w') - vlasovFieldJacobian gradW ρ (s, Φ s)) C w' := by
    intro w' _
    have h1 := hF2 s w'
    have h2 : HasFDerivAt (fun u => vlasovFieldJacobian gradW ρ (s, Φ s) u)
        (vlasovFieldJacobian gradW ρ (s, Φ s)) w' :=
      (vlasovFieldJacobian gradW ρ (s, Φ s)).hasFDerivAt
    exact (h1.sub h2).hasFDerivWithinAt
  have hmv := (convex_closedBall (Φ s) (min δ₀ 1)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hg hbound hΦmem hwmem
  -- Rewrite `g w − g (Φ s)` as the remainder.
  have hReq : (vlasovVectorField gradW ρ s w - vlasovFieldJacobian gradW ρ (s, Φ s) w)
        - (vlasovVectorField gradW ρ s (Φ s) - vlasovFieldJacobian gradW ρ (s, Φ s) (Φ s))
      = vlasovVectorField gradW ρ s w - vlasovVectorField gradW ρ s (Φ s)
        - vlasovFieldJacobian gradW ρ (s, Φ s) (w - Φ s) := by
    rw [map_sub]; abel
  simpa only [hReq] using hmv

/-- **C3 V2 — the explicit fundamental matrix** (Route A, lesson L14): the canonical Dyson-series
solution of `M' = A(t)·M`, `M 0 = id`, as a *function* (not a `choose`-d witness), so its
parameter-regularity is accessible. -/
noncomputable def fundamentalMatrix {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → (F →L[ℝ] F)) : ℝ → (F →L[ℝ] F) :=
  fun t => ∑' n, picardIter (fun s => ContinuousLinearMap.compL ℝ F F F (A s))
    (ContinuousLinearMap.id ℝ F) n t

/-- `fundamentalMatrix A` solves the fundamental-matrix IVP on `[0,T]` (the non-existential form of
`exists_fundamentalMatrix`; same proof through the picardSum lemmas). -/
lemma fundamentalMatrix_spec {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (hA : ContinuousOn A (Set.Icc 0 T)) :
    fundamentalMatrix A 0 = ContinuousLinearMap.id ℝ F ∧
      ContinuousOn (fundamentalMatrix A) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fundamentalMatrix A)
        ((A t).comp (fundamentalMatrix A t)) (Set.Icc 0 T) t := by
  unfold fundamentalMatrix
  simpa only [ContinuousLinearMap.compL_apply] using
    picardSum_spec (fun s => ContinuousLinearMap.compL ℝ F F F (A s)) T hT
      ((ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA)
      (ContinuousLinearMap.id ℝ F)

/-- **C3 V2 — the fundamental matrix is continuous in a PARAMETER** (closes V2 via Route A).
Specialises `picardSum_continuous_param_Icc` to `𝒜 := compL∘A`, `x₀ := id`; the `compL` factor is
`1`-bounded so the `K`-bound transfers from `A`. -/
lemma fundamentalMatrix_continuous_param
    {Z F : Type*} [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : Z → ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hA_contOn : ContinuousOn (fun p : Z × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T))
    (hA_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖A z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (fun z => fundamentalMatrix (A z) t) := by
  have h𝒜_contOn : ContinuousOn
      (fun p : Z × ℝ => ContinuousLinearMap.compL ℝ F F F (A p.1 p.2))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA_contOn
  have h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖ContinuousLinearMap.compL ℝ F F F (A z s)‖ ≤ K := by
    intro z s hs
    refine le_trans ?_ (hA_bound z s hs)
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
    rw [ContinuousLinearMap.compL_apply]
    exact (A z s).opNorm_comp_le g
  exact picardSum_continuous_param_Icc (fun z s => ContinuousLinearMap.compL ℝ F F F (A z s))
    (ContinuousLinearMap.id ℝ F) T hT K hK h𝒜_contOn h𝒜_bound t ht

/-- **Step 3 (i) — the fundamental matrix is jointly `(z,s)`-continuous.**  Joint companion of
`fundamentalMatrix_continuous_param`; specialises `picardSum_continuous_param_Icc_joint` to
`𝒜 := compL∘A`, `x₀ := id`.  This is the partial-`z`-derivative continuity input to the joint
`C¹`-ness of the forward flow `(s,z) ↦ Φ_s z` (Step 3 (iii)). -/
lemma fundamentalMatrix_continuous_param_joint
    {Z F : Type*} [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : Z → ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hA_contOn : ContinuousOn (fun p : Z × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T))
    (hA_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖A z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => fundamentalMatrix (A p.1) p.2)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
  have h𝒜_contOn : ContinuousOn
      (fun p : Z × ℝ => ContinuousLinearMap.compL ℝ F F F (A p.1 p.2))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA_contOn
  have h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖ContinuousLinearMap.compL ℝ F F F (A z s)‖ ≤ K := by
    intro z s hs
    refine le_trans ?_ (hA_bound z s hs)
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
    rw [ContinuousLinearMap.compL_apply]
    exact (A z s).opNorm_comp_le g
  exact picardSum_continuous_param_Icc_joint
    (fun z s => ContinuousLinearMap.compL ℝ F F F (A z s))
    (ContinuousLinearMap.id ℝ F) T hT K hK h𝒜_contOn h𝒜_bound

section CharFlowDeriv
open Filter Topology

omit [NeZero d] in
/-- **C3 D1 — the difference-quotient heart of the variational equation.**

Given the fundamental matrix `Mz` of the linear variational ODE `M' = A(s, Φ_s z)·M`, `M 0 = id`
(coefficient `A = vlasovFieldJacobian`), the time-`t` flow map `w ↦ (charX t w, charV t w)` is
Fréchet-differentiable **at the fixed point `z`** with derivative exactly `Mz t`.

This is the load-bearing difference-quotient estimate `Φ_t(z+h) − Φ_t(z) − Mz t·h = o(‖h‖)`.
The matrix is threaded as an explicit hypothesis (rather than `choose`-d) so the proof can use its
ODE/continuity data directly.

**Proof plan (route b — Grönwall on the linearisation remainder).**  Reduce via
`hasFDerivAt_iff_isLittleO_nhds_zero` + `Asymptotics.isLittleO_iff` to: `∀ c>0, ∀ᶠ h, ‖Φ_t(z+h) −
Φ_t(z) − Mz t·h‖ ≤ c‖h‖`.  For fixed small `h`, the two curves `u_h(s) := Φ_s(z+h) − Φ_s(z)`
(approximate) and `m_h(s) := Mz s·h` (exact) both solve `w' = A(s, Φ_s z)·w` from the same datum
`h` (`Φ_0 = id`, `Mz 0 = id`):
* `m_h` is exact — its defect is `0` (its derivative `(A·Mz)(s)·h = A(s)·m_h(s)` by `hMzderiv` +
  `HasDerivWithinAt.clm_apply`).
* `u_h`'s defect is the Taylor remainder `R(s, Φ_s(z+h))`, bounded by `η·‖u_h(s)‖` (D1a,
  `vlasovField_taylorRemainder_uniform`) once `‖u_h(s)‖ ≤ δ(η)`, which holds with
  `‖u_h(s)‖ ≤ exp(K T)·‖h‖` (flow Lipschitz-in-`z`, `charFlow_lipschitzInZ_via_gronwall_Ioo`) for
  `‖h‖` small.  So `εf = η·exp(K T)·‖h‖`, uniform in `s`.
The frozen field's two-sided ODE holds only on `Ioo 0 T`, so apply
`dist_le_of_approx_trajectories_ODE` on `[s₀, t]` (`s₀ ∈ Ioo 0 t`) and take `s₀ → 0⁺` (the initial
defect `dist(u_h s₀, m_h s₀) → 0` by continuity), giving `‖u_h t − m_h t‖ ≤ gronwallBound 0 K εf t =
εf·(exp(K t)−1)/K`.  Since `η` is arbitrary this is `o(‖h‖)`.  `K := max 1 L` is the uniform field
Lipschitz constant; `‖A(s,·)‖ ≤ K` via `norm_fderiv_le_of_lipschitz`.  (`hcontIcc` is universal in
the initial point because the `s₀→0⁺` limit needs continuity of `Φ_·(z+h)`, M2.) -/
theorem charFlow_hasFDerivAt_of_fundamentalMatrix
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (z : PhaseSpace d)
    (hcontIcc : ∀ z' : PhaseSpace d,
      ContinuousOn (fun s => (charX s z', charV s z')) (Set.Icc (0 : ℝ) T))
    (Mz : ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d))
    (hMz0 : Mz 0 = ContinuousLinearMap.id ℝ (PhaseSpace d))
    (hMzcont : ContinuousOn Mz (Set.Icc 0 T))
    (hMzderiv : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt Mz
        ((vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z))).comp (Mz s))
        (Set.Icc 0 T) s) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, HasFDerivAt (fun w => (charX t w, charV t w)) (Mz t) z := by
  intro t ht
  set Kr : ℝ := ((max 1 L : NNReal) : ℝ) with hKr
  have hKr1 : (1:ℝ) ≤ Kr := by rw [hKr]; exact_mod_cast le_max_left 1 L
  have hKrpos : (0 : ℝ) < Kr := lt_of_lt_of_le one_pos hKr1
  set Φ : ℝ → PhaseSpace d := fun s => (charX s z, charV s z) with hΦ
  have hF2 : ∀ s (w : PhaseSpace d),
      HasFDerivAt (vlasovVectorField gradW ρ s) (vlasovFieldJacobian gradW ρ (s, w)) w :=
    fun s w => vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s w
  have hVF_lip : ∀ s, LipschitzWith (max 1 L) (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  set vlin : ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) := fun s => vlasovFieldJacobian gradW ρ (s, Φ s)
    with hvlin
  have hvlin_norm : ∀ s, ‖vlin s‖ ≤ Kr := by
    intro s
    change ‖vlasovFieldJacobian gradW ρ (s, Φ s)‖ ≤ Kr
    rw [← (hF2 s (Φ s)).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (hVF_lip s)
  have hvlin_lip : ∀ s, LipschitzWith (max 1 L) (vlin s) := by
    intro s
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖vlin s (x - y)‖ ≤ ‖vlin s‖ * ‖x - y‖ := (vlin s).le_opNorm _
      _ ≤ Kr * ‖x - y‖ := mul_le_mul_of_nonneg_right (hvlin_norm s) (norm_nonneg _)
  clear_value vlin
  have h_init : ∀ z' : PhaseSpace d, (charX 0 z', charV 0 z') = z' := fun z' =>
    Prod.ext_iff.mpr ⟨(hflow.1 z' (Set.mem_univ z')).1, (hflow.1 z' (Set.mem_univ z')).2⟩
  have h_derivAt : ∀ z', ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => (charX s z', charV s z'))
        (vlasovVectorField gradW ρ s (charX s z', charV s z')) s := fun z' s hs =>
    HasDerivAt.prodMk (hflow.2.1 s hs z' (Set.mem_univ z')) (hflow.2.2 s hs z' (Set.mem_univ z'))
  have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
    h_init hcontIcc (fun z' s hs => (h_derivAt z' s hs).hasDerivWithinAt)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set Cexp : ℝ := Real.exp (Kr * T) with hCexp
  have hCexp_pos : 0 < Cexp := Real.exp_pos _
  set Cgron : ℝ := (Real.exp (Kr * t) - 1) / Kr with hCgron
  have hCgron_nonneg : 0 ≤ Cgron := by
    rw [hCgron]; apply div_nonneg _ hKrpos.le
    simp only [sub_nonneg]; exact Real.one_le_exp (mul_nonneg hKrpos.le ht.1.le)
  set G : ℝ := Cexp * Cgron with hG
  have hG_nonneg : 0 ≤ G := mul_nonneg hCexp_pos.le hCgron_nonneg
  set η : ℝ := c / (G + 1) with hη
  have hη_pos : 0 < η := by rw [hη]; positivity
  obtain ⟨δη, hδη_pos, hδη⟩ := vlasovField_taylorRemainder_uniform gradW hgradW_C1 L hL ρ h_int
    charX charV T z (hcontIcc z) hρD_cont η hη_pos
  refine Metric.eventually_nhds_iff.mpr
    ⟨δη / (Cexp + 1), div_pos hδη_pos (by linarith [hCexp_pos]), ?_⟩
  intro h hh
  rw [dist_zero_right] at hh
  have hCexph : Cexp * ‖h‖ ≤ δη := by
    have hle : ‖h‖ * (Cexp + 1) ≤ δη := by rw [← le_div_iff₀ (by linarith [hCexp_pos])]; exact hh.le
    nlinarith [norm_nonneg h, hCexp_pos, hle]
  set uh : ℝ → PhaseSpace d := fun s => (charX s (z + h), charV s (z + h)) - (charX s z, charV s z)
    with huh
  set mh : ℝ → PhaseSpace d := fun s => (Mz s) h with hmh
  set εf : ℝ := η * Cexp * ‖h‖ with hεf
  have huh_cont : ContinuousOn uh (Set.Icc 0 T) := (hcontIcc (z + h)).sub (hcontIcc z)
  have hmh_cont : ContinuousOn mh (Set.Icc 0 T) := hMzcont.clm_apply continuousOn_const
  have huh_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖uh s‖ ≤ Cexp * ‖h‖ := by
    intro s hs
    change ‖(charX s (z + h), charV s (z + h)) - (charX s z, charV s z)‖ ≤ Cexp * ‖h‖
    rw [← dist_eq_norm]
    calc dist ((charX s (z + h), charV s (z + h)) : PhaseSpace d) (charX s z, charV s z)
        ≤ dist (z + h) z * Real.exp (Kr * (s - 0)) := hgron s hs (z + h) z
      _ = ‖h‖ * Real.exp (Kr * s) := by rw [dist_eq_norm, add_sub_cancel_left, sub_zero]
      _ ≤ ‖h‖ * Cexp := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg h)
          rw [hCexp]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hKrpos.le)
      _ = Cexp * ‖h‖ := mul_comm _ _
  have huh_derivAt : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt uh
      (vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) s := fun s hs =>
    (h_derivAt (z + h) s hs).sub (h_derivAt z s hs)
  have hmh_derivAt : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt mh ((vlin s) (mh s)) s := by
    intro s hs
    have hMz_at : HasDerivAt Mz ((vlin s).comp (Mz s)) s := by
      simp only [hvlin]
      exact (hMzderiv s (Set.Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hck := hMz_at.clm_apply (hasDerivAt_const s h)
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using hck
  have hdefect : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      dist (vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) (vlin s (uh s)) ≤ εf := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hs
    have huhs_le : ‖uh s‖ ≤ δη := le_trans (huh_bound s hsIcc) hCexph
    have hR := hδη s hsIcc (charX s (z + h), charV s (z + h)) huhs_le
    rw [dist_eq_norm]; simp only [hvlin]
    calc ‖vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
            - vlasovVectorField gradW ρ s (charX s z, charV s z)
            - vlasovFieldJacobian gradW ρ (s, Φ s) (uh s)‖
        ≤ η * ‖uh s‖ := hR
      _ ≤ η * (Cexp * ‖h‖) := mul_le_mul_of_nonneg_left (huh_bound s hsIcc) hη_pos.le
      _ = εf := by rw [hεf]; ring
  have huh0 : uh 0 = h := by
    change (charX 0 (z + h), charV 0 (z + h)) - (charX 0 z, charV 0 z) = h
    rw [h_init (z + h), h_init z, add_sub_cancel_left]
  have hmh0 : mh 0 = h := by change (Mz 0) h = h; rw [hMz0]; rfl
  have hlim : dist (uh t) (mh t) ≤ gronwallBound 0 Kr εf t := by
    have := gronwall_diffQuotient_bound vlin (max 1 L) hvlin_lip uh mh
      (fun s => vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) εf T t ht
      huh_cont hmh_cont huh_derivAt hmh_derivAt hdefect (huh0.trans hmh0.symm)
    rwa [← hKr] at this
  have hgb_val : gronwallBound 0 Kr εf t = εf * Cgron := by
    rw [gronwallBound_of_K_ne_0 hKrpos.ne']; simp only [zero_mul, zero_add]; rw [hCgron]; ring
  have hηG : η * G ≤ c := by
    rw [hη]; rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith [hG_nonneg] : (0 : ℝ) < G + 1)]
    nlinarith [hG_nonneg, hc.le]
  change ‖(charX t (z + h), charV t (z + h)) - (charX t z, charV t z) - (Mz t) h‖ ≤ c * ‖h‖
  rw [show (charX t (z + h), charV t (z + h)) - (charX t z, charV t z) - (Mz t) h
      = uh t - mh t from rfl, ← dist_eq_norm]
  calc dist (uh t) (mh t)
      ≤ gronwallBound 0 Kr εf t := hlim
    _ = εf * Cgron := hgb_val
    _ = η * G * ‖h‖ := by rw [hεf, hG]; ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hηG (norm_nonneg h)

end CharFlowDeriv

omit [NeZero d] in
/-- **C3 #3 — the variational equation (`HasFDerivAt` of the flow in its initial point).**

For the frozen field `b(t,·) = vlasovVectorField gradW ρ t` with `gradW ∈ C¹` (supplied by the
consumer via `assW2_contDiff_gradW`), the time-`t` characteristic map
`z ↦ (charX t z, charV t z)` is Fréchet-differentiable in the initial point `z`, with a derivative
`Dflow t z` that is continuous in `z` (so the flow map is `C¹` in `z`).  The derivative solves the
linear matrix variational ODE `M' = (D_z b(t, Φ_t z)) · M`, `M_0 = id`.

**This was the load-bearing research gap** — Mathlib has no C¹-dependence-of-an-ODE-flow-on-its-
initial-condition lemma — now proven (axiom-clean) via route (b)
(`charFlow_lipschitzInZ_via_gronwall_Ioo`, `CharacteristicFlow.lean`, is the Lipschitz-in-`z`
scaffold; Mathlib Gronwall + the vendored `IsPicardLindelof` confinement are the analytic inputs):
3.1 existence/uniqueness of the continuous matrix solution `M_t(z)` of the variational ODE
(`fundamentalMatrix`); 3.2 joint `(t,z)` continuity of `M` (`fundamentalMatrix_continuous_param`);
3.3 the difference-quotient estimate `Φ_t(z+h) − Φ_t(z) − M_t(z)·h = o(‖h‖)` uniformly on compacts
(Gronwall on the linearization remainder, using `gradW ∈ C¹`,
`charFlow_hasFDerivAt_of_fundamentalMatrix`); 3.4 assembled into `HasFDerivAt`.

The `HasFDerivAt`/continuity *conclusion* is route-independent, so this interface is stable; the
universal-`t` probability instance + force-integrability `h_int` are the field-regularity inputs
the proof consumes (the window-only application clamps, L11, at the grind).

**`hρD_cont` (joint continuity of the convolution-derivative field).**  This is the regularity that
makes the variational coefficient `A(s,z) = D_z b(s, Φ_s z)` continuous in `s` — its only non-flow
varying part is `D_x conv(ρ_s)(x) = ∫ fderiv gradW (x − y) ∂ρ_s`, evaluated at the *moving* point
`Φ_s z`, so per-`x` continuity is not enough; joint `(s,x)`-continuity is needed.  Note the
asymmetry with the *field*: `∫ gradW(x−y) dρ_s` gets joint continuity for free (per-`x` continuity
+ uniform Lipschitz-in-`x`, `convolveFunctionMeasure_lipschitz_in_x`), but the *derivative* field is
NOT uniformly Lipschitz in `x` (that needs `W ∈ C³`; `AssW2` gives only `C²`), so its joint
continuity must be supplied.

**Option-B note (running — eventual extension).**  `hρD_cont` is, in the complete theory, NOT a new
assumption: it is *derivable* from **narrow continuity of `s ↦ ρ_s`** (since `fderiv gradW` is
bounded continuous, `‖·‖ ≤ L`), which is in turn derivable from `IsVlasovSolutionOn` + tightness
(the uniform moment bound) via the standard **"`C_c^∞`-continuity + tight ⟹ narrow-continuity"**
upgrade — a self-contained measure-theory lemma not yet in the codebase.  We thread it as a
hypothesis (Option A) to unblock the variational-equation grind; folding it into a derived fact
(so the bridge assumes only the weak solution + moments) is the **Option-B extension**, tracked as
a follow-up. -/
theorem charFlow_hasFDerivAt_in_initialPoint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∃ Dflow : ℝ → PhaseSpace d → (PhaseSpace d →L[ℝ] PhaseSpace d),
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z : PhaseSpace d,
        HasFDerivAt (fun w => (charX t w, charV t w)) (Dflow t z) z) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, Continuous (Dflow t)) := by
  -- **Reduction (Route A — explicit fundamental matrix, lesson L14).**  `M z := fundamentalMatrix
  -- (A z)` with `A z s := vlasovFieldJacobian gradW ρ (s, Φ_s z)`; its ODE/continuity
  -- data come from
  -- `fundamentalMatrix_spec` (feeds D1), and `z ↦ M z t` continuity (V2) from
  -- `fundamentalMatrix_continuous_param` — the parameter-regularity an existential
  -- `choose` could not
  -- supply.  `Dflow t z := fundamentalMatrix (A z) t`.
  set A : PhaseSpace d → ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun z s => vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z)) with hA_def
  have hAcont : ∀ z : PhaseSpace d, ContinuousOn (A z) (Set.Icc 0 T) := fun z =>
    vlasovVariationalCoeff_continuousOn gradW ρ charX charV T z (hcontIcc z) hρD_cont
  refine ⟨fun t z => fundamentalMatrix (A z) t, ?_, ?_⟩
  · -- **D1** — `charFlow_hasFDerivAt_of_fundamentalMatrix` fed by `fundamentalMatrix_spec`.
    intro t ht z
    obtain ⟨h0, hcont, hderiv⟩ := fundamentalMatrix_spec (A z) T hT.le (hAcont z)
    exact charFlow_hasFDerivAt_of_fundamentalMatrix gradW hgradW_C1 L hL ρ charX charV T hT hflow
      h_int hρD_cont z hcontIcc (fundamentalMatrix (A z)) h0 hcont hderiv t ht
  · -- **V2** — `fundamentalMatrix_continuous_param`: flow joint continuity ⇒ `A` jointly continuous
    -- ⇒ `z ↦ M z t` continuous.
    intro t ht
    -- Flow joint continuity `(z,s) ↦ Φ_s z` on `univ ×ˢ Icc 0 T` (Grönwall Lipschitz-in-`z` from
    -- `hflow` + per-`z` continuity in `s`).
    have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
      Prod.ext_iff.mpr ⟨(hflow.1 z (Set.mem_univ z)).1, (hflow.1 z (Set.mem_univ z)).2⟩
    have h_deriv : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
      (HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z))
        (hflow.2.2 s hs z (Set.mem_univ z))).hasDerivWithinAt
    have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
      h_init hcontIcc h_deriv
    have hflowjoint : ContinuousOn
        (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1)) (Set.univ ×ˢ Set.Icc 0 T) := by
      refine continuousOn_prod_of_lipschitz_continuousOn (fun z s => (charX s z, charV s z)) T
        (Real.exp (((max 1 L : NNReal) : ℝ) * T)) (fun s hs z₁ z₂ => ?_) hcontIcc
      calc dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
          ≤ dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) := hgron s hs z₁ z₂
        _ = Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) * dist z₁ z₂ := by ring
        _ ≤ Real.exp (((max 1 L : NNReal) : ℝ) * T) * dist z₁ z₂ := by
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) dist_nonneg
            have hsT : s - 0 ≤ T := by simp only [sub_zero]; exact hs.2
            exact mul_le_mul_of_nonneg_left hsT (by positivity)
    -- `A` jointly continuous (Jacobian along the flow) and uniformly bounded by `max 1 L`.
    have hg : ContinuousOn
        (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) := continuousOn_snd.prodMk hflowjoint
    have hmapsg : Set.MapsTo
        (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
    have hA_contOn : ContinuousOn (fun p : PhaseSpace d × ℝ => A p.1 p.2)
        (Set.univ ×ˢ Set.Icc 0 T) :=
      (vlasovFieldJacobian_continuousOn gradW ρ T hρD_cont).comp hg hmapsg
    have hA_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖A z s‖ ≤ ((max 1 L : NNReal) : ℝ) := by
      intro z s _
      have heq : A z s = fderiv ℝ (vlasovVectorField gradW ρ s) (charX s z, charV s z) := by
        simp only [hA_def]
        exact (vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s
          (charX s z, charV s z)).fderiv.symm
      rw [heq]
      exact norm_fderiv_le_of_lipschitz ℝ (vlasovVectorField_lipschitzWith gradW L hL ρ h_int s)
    exact fundamentalMatrix_continuous_param A T hT.le ((max 1 L : NNReal) : ℝ) (by positivity)
      hA_contOn hA_bound t (Set.Ioo_subset_Icc_self ht)

open Filter Topology in
omit [NeZero d] in
/-- **Step 1 (dual core) — lower Grönwall / anti-Lipschitz bound on the characteristic flow.**
For `t ∈ (0,T)`, the flow `Φ_t : z ↦ (charX t z, charV t z)` satisfies
`dist z₁ z₂ ≤ dist (Φ_t z₁) (Φ_t z₂) · exp(K t)` (K = max 1 L), i.e. `Φ_t` is `AntilipschitzWith`.
This is the keystone of the two-time-flow inverse construction (Step 2): bi-Lipschitz makes `Φ_t`
injective with closed range and `M_t = DΦ_t` invertible (no Liouville needed).

Proof: time-reverse the two trajectories on each `[s₀,t] ⊆ (0,T)` (so they solve
`w' = −b_{s₀+t−r}(w)`, still K-Lipschitz) and apply the existing forward
`dist_le_of_trajectories_ODE`; take `s₀→0⁺`.  `h_deriv2` is the two-sided `HasDerivAt` on the open
interval, supplied by `IsCharacteristicFlowOn`. -/
theorem charFlow_antilipschitzInZ_via_gronwall_Ioo
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z, ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv2 : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤
        dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂)
          * Real.exp (((max 1 L : NNReal) : ℝ) * (t - 0)) := by
  intro t ht z₁ z₂
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  set F : ℝ → PhaseSpace d := fun s => (charX s z₁, charV s z₁) with hF_def
  set G : ℝ → PhaseSpace d := fun s => (charX s z₂, charV s z₂) with hG_def
  -- Per-`s₀` antilipschitz bound on `[s₀, t]`.
  have h_perS0 : ∀ s₀ ∈ Set.Ioo (0 : ℝ) t,
      dist (F s₀) (G s₀) ≤ dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀)) := by
    intro s₀ hs₀
    have hsub_Ioo : Set.Icc s₀ t ⊆ Set.Ioo (0 : ℝ) T := fun r hr =>
      ⟨lt_of_lt_of_le hs₀.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    have hsub_Icc : Set.Icc s₀ t ⊆ Set.Icc (0 : ℝ) T := fun r hr =>
      ⟨le_of_lt (lt_of_lt_of_le hs₀.1 hr.1), le_of_lt (lt_of_le_of_lt hr.2 ht.2)⟩
    have hrefl_mem : ∀ r ∈ Set.Icc s₀ t, s₀ + t - r ∈ Set.Icc s₀ t := by
      intro r hr; exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hrefl_cont : ContinuousOn (fun r : ℝ => s₀ + t - r) (Set.Icc s₀ t) :=
      (continuous_const.sub continuous_id).continuousOn
    set vr : ℝ → PhaseSpace d → PhaseSpace d :=
      fun r w => -(vlasovVectorField gradW ρ (s₀ + t - r) w) with hvr_def
    have hvr_lip : ∀ r, LipschitzWith K (vr r) := fun r => (h_vf_lip (s₀ + t - r)).neg
    have hFr_cont : ContinuousOn (fun r => F (s₀ + t - r)) (Set.Icc s₀ t) :=
      (h_cont_Icc z₁).comp hrefl_cont (fun r hr => hsub_Icc (hrefl_mem r hr))
    have hGr_cont : ContinuousOn (fun r => G (s₀ + t - r)) (Set.Icc s₀ t) :=
      (h_cont_Icc z₂).comp hrefl_cont (fun r hr => hsub_Icc (hrefl_mem r hr))
    have hFr' : ∀ r ∈ Set.Ico s₀ t,
        HasDerivWithinAt (fun r => F (s₀ + t - r)) (vr r (F (s₀ + t - r))) (Set.Ici r) r := by
      intro r hr
      have hrIoo : s₀ + t - r ∈ Set.Ioo (0 : ℝ) T :=
        hsub_Ioo ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hlin : HasDerivAt (fun r : ℝ => s₀ + t - r) (-1) r := by
        simpa using (hasDerivAt_id r).const_sub (s₀ + t)
      have key : HasDerivAt (fun r => F (s₀ + t - r))
          ((-1 : ℝ) • vlasovVectorField gradW ρ (s₀ + t - r) (F (s₀ + t - r))) r :=
        HasDerivAt.scomp_of_eq r (h_deriv2 z₁ (s₀ + t - r) hrIoo) hlin rfl
      simp only [neg_one_smul] at key
      exact key.hasDerivWithinAt
    have hGr' : ∀ r ∈ Set.Ico s₀ t,
        HasDerivWithinAt (fun r => G (s₀ + t - r)) (vr r (G (s₀ + t - r))) (Set.Ici r) r := by
      intro r hr
      have hrIoo : s₀ + t - r ∈ Set.Ioo (0 : ℝ) T :=
        hsub_Ioo ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hlin : HasDerivAt (fun r : ℝ => s₀ + t - r) (-1) r := by
        simpa using (hasDerivAt_id r).const_sub (s₀ + t)
      have key : HasDerivAt (fun r => G (s₀ + t - r))
          ((-1 : ℝ) • vlasovVectorField gradW ρ (s₀ + t - r) (G (s₀ + t - r))) r :=
        HasDerivAt.scomp_of_eq r (h_deriv2 z₂ (s₀ + t - r) hrIoo) hlin rfl
      simp only [neg_one_smul] at key
      exact key.hasDerivWithinAt
    have hgron := dist_le_of_trajectories_ODE hvr_lip hFr_cont hFr' hGr_cont hGr'
      (le_refl (dist (F (s₀ + t - s₀)) (G (s₀ + t - s₀)))) t ⟨hs₀.2.le, le_refl t⟩
    simp only [show s₀ + t - t = s₀ from by ring, show s₀ + t - s₀ = t from by ring] at hgron
    exact hgron
  -- `s₀ → 0⁺` limit.
  have hfilt : (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)).NeBot := left_nhdsWithin_Ioo_neBot ht.1
  have hIoo_sub_Icc : Set.Ioo (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun s hs =>
    ⟨hs.1.le, le_of_lt (lt_trans hs.2 ht.2)⟩
  have h_tendsto_F : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds z₁) := by
    have hcw : ContinuousWithinAt F (Set.Icc (0 : ℝ) T) 0 :=
      (h_cont_Icc z₁) 0 ⟨le_refl 0, le_of_lt (lt_trans ht.1 ht.2)⟩
    have h0 : Tendsto F (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (F 0)) := hcw
    rw [show F 0 = z₁ from h_init z₁] at h0
    exact h0.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
  have h_tendsto_G : Tendsto G (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds z₂) := by
    have hcw : ContinuousWithinAt G (Set.Icc (0 : ℝ) T) 0 :=
      (h_cont_Icc z₂) 0 ⟨le_refl 0, le_of_lt (lt_trans ht.1 ht.2)⟩
    have h0 : Tendsto G (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (G 0)) := hcw
    rw [show G 0 = z₂ from h_init z₂] at h0
    exact h0.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
  have h_tendsto_lhs : Tendsto (fun s₀ => dist (F s₀) (G s₀))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds (dist z₁ z₂)) :=
    h_tendsto_F.dist h_tendsto_G
  have h_tendsto_rhs : Tendsto (fun s₀ => dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀)))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
      (nhds (dist (F t) (G t) * Real.exp ((K : ℝ) * (t - 0)))) := by
    have hcont : Continuous (fun s₀ : ℝ => dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀))) := by
      fun_prop
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto h_tendsto_lhs h_tendsto_rhs
    (eventually_nhdsWithin_of_forall h_perS0)

section Step2Inverse
open Filter Topology

/-- **Step 2a (dual core, generic) — antilipschitz map ⇒ antilipschitz derivative.**
If `f` is antilipschitz and Fréchet-differentiable at `x`, its derivative `f'` is antilipschitz
(hence injective) with the same constant.  `f' u` is the limit of slopes `n•(f(x+n⁻¹•u)−f x)`, each
of norm `≥ ‖u‖/C` by antilipschitz; pass to the limit.  (Mathlib lacks this producer.) -/
theorem antilipschitzWith_fderiv_of_antilipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {x : E} {C : NNReal}
    (hf : AntilipschitzWith C f) (hf' : HasFDerivAt f f' x) :
    AntilipschitzWith C f' := by
  refine AntilipschitzWith.of_le_mul_dist (fun v w => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  set u := v - w with hu
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ))‖) atTop atTop := by
    simpa [Real.norm_natCast] using tendsto_natCast_atTop_atTop (R := ℝ)
  have hlim := hf'.lim u hc
  have hbd : ∀ᶠ n : ℕ in atTop,
      ‖u‖ ≤ (C : ℝ) * ‖(n : ℝ) • (f (x + ((n : ℝ))⁻¹ • u) - f x)‖ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hd := hf.le_mul_dist (x + ((n : ℝ))⁻¹ • u) x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv,
      Real.norm_natCast] at hd
    rw [norm_smul, Real.norm_natCast]
    calc ‖u‖ = (n : ℝ) * ((n : ℝ)⁻¹ * ‖u‖) := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn0), one_mul]
      _ ≤ (n : ℝ) * ((C : ℝ) * ‖f (x + ((n : ℝ))⁻¹ • u) - f x‖) :=
              mul_le_mul_of_nonneg_left hd (le_of_lt hn0)
      _ = (C : ℝ) * ((n : ℝ) * ‖f (x + ((n : ℝ))⁻¹ • u) - f x‖) := by ring
  have hlim2 : Tendsto (fun n : ℕ => (C : ℝ) * ‖(n : ℝ) • (f (x + ((n : ℝ))⁻¹ • u) - f x)‖)
      atTop (𝓝 ((C : ℝ) * ‖f' u‖)) := hlim.norm.const_mul (C : ℝ)
  exact ge_of_tendsto hlim2 hbd

/-- **Step 2 (dual core, generic) — global `C¹` inverse of an antilipschitz `C¹` self-map.**
If `Φ : E → E` (finite-dim) is `C¹` (derivative `M z` at `z`), antilipschitz, and Lipschitz, then
each `M z` is invertible, `Φ` is bijective, and the global inverse `Ψ` is Lipschitz with
`HasFDerivAt Ψ (M (Ψ w))⁻¹ w`.  No Liouville/Hadamard: open range
(`isOpenMap_of_hasStrictFDerivAt_equiv`) + closed range (`AntilipschitzWith.isClosed_range`) ⇒
clopen ⇒ surjective; inverse derivative from `HasStrictFDerivAt.to_local_left_inverse`. -/
theorem exists_global_c1_inverse_of_antilipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Φ : E → E} {M : E → (E →L[ℝ] E)} {Ca Cl : NNReal}
    (hderiv : ∀ z, HasFDerivAt Φ (M z) z)
    (hM_cont : Continuous M)
    (hanti : AntilipschitzWith Ca Φ)
    (hlip : LipschitzWith Cl Φ) :
    ∃ (Ψ : E → E) (e : E → E ≃L[ℝ] E),
      (∀ z, ((e z : E →L[ℝ] E)) = M z) ∧
      Function.LeftInverse Ψ Φ ∧ Function.RightInverse Ψ Φ ∧
      LipschitzWith Ca Ψ ∧
      (∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : E →L[ℝ] E) w) := by
  classical
  have hMz_anti : ∀ z, AntilipschitzWith Ca (M z) := fun z =>
    antilipschitzWith_fderiv_of_antilipschitz hanti (hderiv z)
  have hker : ∀ z, LinearMap.ker (M z : E →ₗ[ℝ] E) = ⊥ := fun z =>
    LinearMap.ker_eq_bot.mpr (hMz_anti z).injective
  have hsurj_lin : ∀ z, LinearMap.range (M z : E →ₗ[ℝ] E) = ⊤ := fun z =>
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp (hMz_anti z).injective)
  set e : ∀ z, E ≃L[ℝ] E := fun z =>
    ContinuousLinearEquiv.ofBijective (M z) (hker z) (hsurj_lin z) with he_def
  have he_coe : ∀ z, ((e z : E →L[ℝ] E)) = M z := fun _ => rfl
  have hC1 : ContDiff ℝ 1 Φ := contDiff_one_iff_hasFDerivAt.mpr ⟨M, hM_cont, hderiv⟩
  have hstrict : ∀ z, HasStrictFDerivAt Φ ((e z : E →L[ℝ] E)) z := fun z => by
    rw [he_coe z]; exact hC1.contDiffAt.hasStrictFDerivAt' (hderiv z) (by norm_num)
  have hopen : IsOpenMap Φ := isOpenMap_of_hasStrictFDerivAt_equiv hstrict
  have hrange_open : IsOpen (Set.range Φ) := hopen.isOpen_range
  have hrange_closed : IsClosed (Set.range Φ) := hanti.isClosed_range hlip.uniformContinuous
  have hrange_univ : Set.range Φ = Set.univ :=
    IsClopen.eq_univ ⟨hrange_closed, hrange_open⟩ ⟨Φ 0, Set.mem_range_self 0⟩
  have hsurj : Function.Surjective Φ := Set.range_eq_univ.mp hrange_univ
  have hinj : Function.Injective Φ := hanti.injective
  set Ψ : E → E := Function.invFun Φ with hΨ_def
  have hLeft : Function.LeftInverse Ψ Φ := Function.leftInverse_invFun hinj
  have hRight : Function.RightInverse Ψ Φ := Function.rightInverse_invFun hsurj
  have hΨ_lip : LipschitzWith Ca Ψ := by
    refine LipschitzWith.of_dist_le_mul (fun w₁ w₂ => ?_)
    have h := hanti.le_mul_dist (Ψ w₁) (Ψ w₂)
    rwa [hRight w₁, hRight w₂] at h
  have hΨ_deriv : ∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : E →L[ℝ] E) w := by
    intro w
    have hz : Φ (Ψ w) = w := hRight w
    have hev : ∀ᶠ x in 𝓝 (Ψ w), Ψ (Φ x) = x := Filter.Eventually.of_forall hLeft
    have hsymm := (hstrict (Ψ w)).to_local_left_inverse hev
    rw [hz] at hsymm
    exact hsymm.hasFDerivAt
  exact ⟨Ψ, e, he_coe, hLeft, hRight, hΨ_lip, hΨ_deriv⟩

end Step2Inverse

omit [NeZero d] in
/-- **Step 2 (dual core) — the characteristic flow `Φ_t` is a `C¹` diffeomorphism on `(0,T)`.**
Instantiates the generic global-inverse machinery at `Φ_t := (charX t, charV t)`: its derivative
`e z` (= `#3`'s `Dflow t z`) is invertible, `Φ_t` is bijective, and the inverse `Ψ` is continuous
with `HasFDerivAt Ψ (e (Ψ w))⁻¹ w`.  `hanti` comes from Step 1
(`charFlow_antilipschitzInZ_via_gronwall_Ioo`), `hlip` from the existing upper Grönwall bound
(`charFlow_lipschitzInZ_via_gronwall_Ioo`), the derivative family from `#3`. -/
theorem exists_charFlow_inverse_On
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∃ (Ψ : PhaseSpace d → PhaseSpace d)
        (e : PhaseSpace d → (PhaseSpace d ≃L[ℝ] PhaseSpace d)),
        (∀ z, HasFDerivAt (fun w => (charX t w, charV t w))
          ((e z : PhaseSpace d →L[ℝ] PhaseSpace d)) z) ∧
        Function.LeftInverse Ψ (fun z => (charX t z, charV t z)) ∧
        Function.RightInverse Ψ (fun z => (charX t z, charV t z)) ∧
        Continuous Ψ ∧
        (∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : PhaseSpace d →L[ℝ] PhaseSpace d) w) := by
  have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext_iff.mpr (hflow.1 z (Set.mem_univ z))
  have h_deriv2 : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s := fun z s hs =>
    HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z)) (hflow.2.2 s hs z (Set.mem_univ z))
  have h_deriv_Ioo : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
    (h_deriv2 z s hs).hasDerivWithinAt
  obtain ⟨Dflow, hDeriv, hCont⟩ := charFlow_hasFDerivAt_in_initialPoint gradW hgradW_C1 L hL ρ
    charX charV T hT hflow h_int hρD_cont hcontIcc
  intro t ht
  set K : ℝ := ((max 1 L : NNReal) : ℝ) with hK
  have hCcoe : (((Real.exp (K * t)).toNNReal : NNReal) : ℝ) = Real.exp (K * t) :=
    Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _))
  have hderiv : ∀ z, HasFDerivAt (fun z => (charX t z, charV t z)) (Dflow t z) z := fun z =>
    hDeriv t ht z
  have hM_cont : Continuous (Dflow t) := hCont t ht
  have hanti : AntilipschitzWith (Real.exp (K * t)).toNNReal
      (fun z => (charX t z, charV t z)) := by
    refine AntilipschitzWith.of_le_mul_dist (fun z₁ z₂ => ?_)
    have h1 := charFlow_antilipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T
      h_init hcontIcc h_deriv2 t ht z₁ z₂
    rw [sub_zero] at h1
    rw [hCcoe, mul_comm]
    exact h1
  have hlip : LipschitzWith (Real.exp (K * t)).toNNReal
      (fun z => (charX t z, charV t z)) := by
    refine LipschitzWith.of_dist_le_mul (fun z₁ z₂ => ?_)
    have h1 := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
      h_init hcontIcc h_deriv_Ioo t (Set.Ioo_subset_Icc_self ht) z₁ z₂
    rw [sub_zero] at h1
    rw [hCcoe, mul_comm]
    exact h1
  obtain ⟨Ψ, e, he_coe, hLeft, hRight, hΨlip, hΨderiv⟩ :=
    exists_global_c1_inverse_of_antilipschitz hderiv hM_cont hanti hlip
  refine ⟨Ψ, e, ?_, hLeft, hRight, hΨlip.continuous, hΨderiv⟩
  intro z; rw [he_coe z]; exact hderiv z

section Step3Joint
open Filter Topology Asymptotics


end Step3Joint

omit [NeZero d] in
/-- **Step 3 — the forward flow `(s,z) ↦ Φ_s z` is jointly continuous** on `Icc 0 T ×ˢ univ`
(`(s,z)`-order).  Gronwall Lipschitz-in-`z` (uniform over `[0,T]`) + per-`z` continuity-in-`s`, via
the generic `continuousOn_prod_of_lipschitz_continuousOn`, then a prod-order swap.  Extracted from
`#3`'s V2-branch pattern so the joint `C¹`-ness (Step 3 (iii)) can reuse it directly. -/
lemma charFlow_continuousOn_joint
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (hT : 0 ≤ T)
    (hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (hcontIcc : ∀ z, ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s) :
    ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT
    hinit hcontIcc hderiv
  have hjoint_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
    refine continuousOn_prod_of_lipschitz_continuousOn (fun z s => (charX s z, charV s z)) T
      (Real.exp (((max 1 L : NNReal) : ℝ) * T)) (fun s hs z₁ z₂ => ?_) hcontIcc
    calc dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        ≤ dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) := hgron s hs z₁ z₂
      _ = Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) * dist z₁ z₂ := by ring
      _ ≤ Real.exp (((max 1 L : NNReal) : ℝ) * T) * dist z₁ z₂ := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) dist_nonneg
          have hsT : s - 0 ≤ T := by simp only [sub_zero]; exact hs.2
          exact mul_le_mul_of_nonneg_left hsT (by positivity)
  have hswap : ContinuousOn (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := (continuous_snd.prodMk continuous_fst).continuousOn
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    fun p hp => ⟨Set.mem_univ _, hp.1⟩
  exact hjoint_zs.comp hswap hmaps

omit [NeZero d] in
/-- **Step 3 (ii) — the field along the flow `(s,z) ↦ b_s(Φ_s z)` is jointly continuous** on
`Icc 0 T ×ˢ univ`.  First component `charV` from flow joint continuity; second component
`-(∇W ∗ ρ_s)(charX s z)` from `(s,x) ↦ (∇W∗ρ_s)(x)` jointly continuous (equi-Lipschitz-in-`x` from
`convolveFunctionMeasure_lipschitz_in_x` + continuous-in-`s` from `hf_cont`) composed with the flow.
This is the partial-`s`-derivative continuity input to the joint `C¹`-ness (Step 3 (iii)). -/
lemma vlasovField_along_flow_continuousOn
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ)
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × PhaseSpace d =>
        vlasovVectorField gradW ρ p.1 (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  have hcomp1 : ContinuousOn (fun p : ℝ × PhaseSpace d => charV p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := continuous_snd.comp_continuousOn hflowjoint
  have hcharX : ContinuousOn (fun p : ℝ × PhaseSpace d => charX p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := continuous_fst.comp_continuousOn hflowjoint
  have hconv_joint : ContinuousOn
      (fun p : PhysSpace d × ℝ => convolveFunctionMeasure gradW (ρ p.2) p.1)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    continuousOn_prod_of_lipschitz_continuousOn
      (fun (x : PhysSpace d) (s : ℝ) => convolveFunctionMeasure gradW (ρ s) x) T (L:ℝ)
      (fun s _ x₁ x₂ =>
        (convolveFunctionMeasure_lipschitz_in_x gradW L hL (ρ s) (h_int s)).dist_le_mul x₁ x₂)
      (fun x => (hf_cont x).continuousOn)
  have hg2 : ContinuousOn (fun p : ℝ × PhaseSpace d => ((charX p.1 p.2, p.1) : PhysSpace d × ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := hcharX.prodMk continuousOn_fst
  have hg2maps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((charX p.1 p.2, p.1) : PhysSpace d × ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    fun p hp => ⟨Set.mem_univ _, hp.1⟩
  have hconv_along : ContinuousOn
      (fun p : ℝ × PhaseSpace d => convolveFunctionMeasure gradW (ρ p.1) (charX p.1 p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := hconv_joint.comp hg2 hg2maps
  have heq : (fun p : ℝ × PhaseSpace d =>
        vlasovVectorField gradW ρ p.1 (charX p.1 p.2, charV p.1 p.2))
      = fun p => ((charV p.1 p.2),
          -(convolveFunctionMeasure gradW (ρ p.1) (charX p.1 p.2))) := by
    funext p; rfl
  rw [heq]
  exact hcomp1.prodMk hconv_along.neg

omit [NeZero d] in
/-- **Step 3 (iii) — the forward flow `(s,z) ↦ Φ_s z` is jointly `C¹`** on `U := Ioo 0 T ×ˢ univ`:
Fréchet-differentiable at every point with a jointly-continuous total derivative `DΦ`.  Built by
composing the open-set gating theorem (`hasFDerivAt_of_continuous_partials_open`) — fed the
`s`-partial `b_s(Φ_s z)` (flow ODE, jointly continuous by item (ii)) and the `z`-partial `M_s z`
(the fundamental matrix, via D1c, jointly continuous by item (i)).  Per L14 the matrix is rebuilt
concretely (`fundamentalMatrix (A z) s`), NOT routed through `#3`'s existential.

The field `bfun` and matrix `Mfun` are made opaque locals (`clear_value`, the D1c lesson) so the
gating unification stays syntactic and never unfolds the `vlasovVectorField`/`vlasovFieldJacobian`
integrals — the per-point derivative facts are established in terms of them *before* clearing.
`A` is kept transparent through the D1c call (whose coefficient is
`vlasovFieldJacobian`) and cleared
only afterwards (before the projection-reduction defeqs).  No `maxHeartbeats` bump needed. -/
theorem charFlow_hasFDerivAt_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∃ DΦ : ℝ × PhaseSpace d → (ℝ × PhaseSpace d →L[ℝ] PhaseSpace d),
      (∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
        HasFDerivAt (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) (DΦ p) p) ∧
      ContinuousOn DΦ (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  set A : PhaseSpace d → ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun z s => vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z)) with hA_def
  have hAcont : ∀ z, ContinuousOn (A z) (Set.Icc 0 T) := fun z =>
    vlasovVariationalCoeff_continuousOn gradW ρ charX charV T z (hcontIcc z) hρD_cont
  have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext_iff.mpr ⟨(hflow.1 z (Set.mem_univ z)).1, (hflow.1 z (Set.mem_univ z)).2⟩
  have h_deriv : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
    (HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z))
      (hflow.2.2 s hs z (Set.mem_univ z))).hasDerivWithinAt
  have hflowjoint_sz : ContinuousOn (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2))
      (Set.Icc 0 T ×ˢ Set.univ) :=
    charFlow_continuousOn_joint gradW L hL ρ h_int charX charV T hT.le h_init hcontIcc h_deriv
  -- field as an opaque local
  set bfun : ℝ × PhaseSpace d → PhaseSpace d :=
    fun q => vlasovVectorField gradW ρ q.1 (charX q.1 q.2, charV q.1 q.2) with hbfun_def
  have hb_cont : ContinuousOn bfun (Set.Icc 0 T ×ˢ Set.univ) :=
    vlasovField_along_flow_continuousOn gradW L hL ρ h_int hf_cont charX charV T hflowjoint_sz
  -- `A` jointly continuous + bounded ⇒ `M` jointly continuous (item (i))
  have hflowjoint_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1))
      (Set.univ ×ˢ Set.Icc 0 T) := by
    have hswap : ContinuousOn (fun p : PhaseSpace d × ℝ => ((p.2, p.1) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) := (continuous_snd.prodMk continuous_fst).continuousOn
    have hmaps : Set.MapsTo (fun p : PhaseSpace d × ℝ => ((p.2, p.1) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
    exact hflowjoint_sz.comp hswap hmaps
  have hg : ContinuousOn
      (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
      (Set.univ ×ˢ Set.Icc 0 T) := continuousOn_snd.prodMk hflowjoint_zs
  have hmapsg : Set.MapsTo
      (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
      (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
  have hA_contOn : ContinuousOn (fun p : PhaseSpace d × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc 0 T) :=
    (vlasovFieldJacobian_continuousOn gradW ρ T hρD_cont).comp hg hmapsg
  have hA_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖A z s‖ ≤ ((max 1 L : NNReal) : ℝ) := by
    intro z s _
    have heq : A z s = fderiv ℝ (vlasovVectorField gradW ρ s) (charX s z, charV s z) := by
      simp only [hA_def]
      exact (vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s
        (charX s z, charV s z)).fderiv.symm
    rw [heq]
    exact norm_fderiv_le_of_lipschitz ℝ (vlasovVectorField_lipschitzWith gradW L hL ρ h_int s)
  have hM_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => fundamentalMatrix (A p.1) p.2)
      (Set.univ ×ˢ Set.Icc 0 T) :=
    fundamentalMatrix_continuous_param_joint A T hT.le ((max 1 L : NNReal) : ℝ) (by positivity)
      hA_contOn hA_bound
  have hU_open : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  have hU_sub : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) ⊆ Set.Icc 0 T ×ˢ Set.univ :=
    Set.prod_mono Set.Ioo_subset_Icc_self (subset_refl _)
  -- matrix as a local (kept transparent for the D1c call, which needs `A`'s coefficient)
  set Mfun : ℝ × PhaseSpace d → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun p => fundamentalMatrix (A p.2) p.1 with hMfun_def
  -- z-partial at base via D1c — needs `A` TRANSPARENT (its coefficient is `vlasovFieldJacobian`).
  have hDz_all : ∀ s₀ ∈ Set.Ioo (0 : ℝ) T, ∀ z₀ : PhaseSpace d,
      HasFDerivAt (fun z => (charX s₀ z, charV s₀ z)) (Mfun (s₀, z₀)) z₀ := by
    intro s₀ hs₀ z₀
    obtain ⟨h0, hMcont, hMderiv⟩ := fundamentalMatrix_spec (A z₀) T hT.le (hAcont z₀)
    exact charFlow_hasFDerivAt_of_fundamentalMatrix gradW hgradW_C1 L hL ρ charX charV T hT hflow
      h_int hρD_cont z₀ hcontIcc (fundamentalMatrix (A z₀)) h0 hMcont hMderiv s₀ hs₀
  have hDs_all : ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s => ((charX s p.2, charV s p.2) : PhaseSpace d)) (bfun p) p.1 := by
    intro p hp'
    exact HasDerivAt.prodMk (hflow.2.1 p.1 hp'.1 p.2 (Set.mem_univ _))
      (hflow.2.2 p.1 hp'.1 p.2 (Set.mem_univ _))
  -- NOW make `A`/field/matrix opaque so the projection-reduction defeqs below never unfold the
  -- heavy `vlasovFieldJacobian`/`vlasovVectorField` integrals (D1c lesson).
  clear_value A bfun Mfun
  have hM_sz : ContinuousOn Mfun (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    rw [hMfun_def]
    have hswap : ContinuousOn (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := (continuous_snd.prodMk continuous_fst).continuousOn
    have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc 0 T) :=
      fun p hp => ⟨Set.mem_univ _, Set.Ioo_subset_Icc_self hp.1⟩
    exact hM_zs.comp hswap hmaps
  refine ⟨fun p => (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight (bfun p)
      + (Mfun p).comp (ContinuousLinearMap.snd ℝ ℝ (PhaseSpace d)), ?_, ?_⟩
  · rintro ⟨s₀, z₀⟩ hp
    obtain ⟨hs₀, _⟩ := hp
    exact hasFDerivAt_of_continuous_partials_open
      (f := fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) (Ds := bfun)
      hU_open ⟨hs₀, Set.mem_univ _⟩ hDs_all (hb_cont.mono hU_sub) (hDz_all s₀ hs₀ z₀)
  · have hT1 : ContinuousOn (fun p : ℝ × PhaseSpace d =>
        (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight (bfun p))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
      have hc : Continuous (fun v : PhaseSpace d =>
          (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight v) :=
        (ContinuousLinearMap.smulRightL ℝ (ℝ × PhaseSpace d) (PhaseSpace d)
          (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d))).continuous
      exact hc.comp_continuousOn (hb_cont.mono hU_sub)
    have hT2 : ContinuousOn (fun p : ℝ × PhaseSpace d =>
        (Mfun p).comp (ContinuousLinearMap.snd ℝ ℝ (PhaseSpace d)))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := hM_sz.clm_comp continuousOn_const
    exact hT1.add hT2

omit [NeZero d] in
/-- **Step 3 (iv-A) — the forward flow `(s,z) ↦ Φ_s z` is `ContDiffAt ℝ 1`** at each point of the
open window (the chart-IFT input for item (iv)).  Lifts item (iii)'s `HasFDerivAt`-everywhere +
`ContinuousOn`-derivative to `ContDiffAt` via `contDiffAt_succ_iff_hasFDerivAt`. -/
lemma charFlow_contDiffAt_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
      ContDiffAt ℝ 1 (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) p := by
  obtain ⟨DΦ, hFDeriv, hDΦ_cont⟩ :=
    charFlow_hasFDerivAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hU_open : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  intro p hp
  have hmain : ContDiffAt ℝ ((0:ℕ) + 1)
      (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) p := by
    rw [contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨DΦ, ⟨Set.Ioo (0 : ℝ) T ×ˢ Set.univ, hU_open.mem_nhds hp, fun y hy => hFDeriv y hy⟩, ?_⟩
    exact contDiffAt_zero.mpr ⟨Set.Ioo (0 : ℝ) T ×ˢ Set.univ, hU_open.mem_nhds hp, hDΦ_cont⟩
  simpa using hmain

open Filter Topology in
omit [NeZero d] in
/-- **Step 3 (iv) — the per-slice inverse `Ψ_s := Φ_s⁻¹` is jointly `C¹`** on `Ioo 0 T ×ˢ univ`,
the keystone of the two-time flow `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹`.

**PROVEN (axiom-clean)** via the space-time chart inverse-function theorem — see the proof plan
below, realized exactly as scouted: `charFlow_contDiffAt_joint` (iv-A) for the chart `ContDiffAt`,
the block-triangular `≃L` (invertibility from Step 2's `e z₀` via `HasFDerivAt.unique` +
`ofBijective`), `ContDiffAt.to_localInverse`, and the global patch via `localInverse_unique` (the
global per-slice inverse is a local left inverse of the chart, by injectivity on the window).

Per slice `s ∈ Ioo 0 T`, Step 2 (`exists_charFlow_inverse_On`) already gives the inverse `Ψ_s` and
its invertible derivative family `e` (`= M_s z`, `#3`/D1c); here we upgrade to JOINT `(s,w)`
regularity via the space-time chart.

**Proof plan (atoms scouted + verified, 2026-06-16):**
1. **Forward chart `Ξ : (s,z) ↦ (s, Φ_s z)` is `ContDiffAt ℝ 1` at each
   `(s₀,z₀) ∈ Ioo 0 T ×ˢ univ`.**
   `Φ := (charX·, charV·)` is jointly `C¹` (`charFlow_hasFDerivAt_joint`, item (iii) — `∃ DΦ`,
   `HasFDerivAt`-everywhere + `ContinuousOn DΦ`); lift to `ContDiffAt ℝ 1 Φ` via
   `contDiffAt_succ_iff_hasFDerivAt` (`Mathlib/.../ContDiff/Defs.lean:994`, `n := 0`: feed `DΦ`, the
   open nbhd `U ∈ 𝓝`, `HasFDerivAt`-on-`U`, and `ContDiffAt 0 DΦ` from `contDiffAt_zero` +
   `ContinuousOn DΦ U`).  `Ξ = (fst, Φ)` so `ContDiffAt ℝ 1 Ξ` via `ContDiffAt.prod` with
   `contDiffAt_fst`.
2. **`DΞ(s₀,z₀)` is an invertible `≃L`.**  Block-lower-triangular `(h,k) ↦ (h, h•b + M·k)` with
   `b := b_{s₀}(Φ_{s₀}z₀)`, `M := M_{s₀}z₀` invertible (Step 2's `e₀ z₀`).  Build the `ℝ×E ≃L ℝ×E`
   via `ContinuousLinearEquiv.ofBijective` (inject: `(h,k)↦0 ⇒ h=0`, then `M k=0 ⇒ k=0`; finite-dim
   `LinearMap.injective_iff_surjective`).  `HasStrictFDerivAt Ξ (this ≃L) (s₀,z₀)` via
   `ContDiffAt.hasStrictFDerivAt'`.
3. **Local `C¹` inverse + patch.**  `ContDiffAt.to_localInverse`
   (`Mathlib/.../InverseFunctionTheorem/ContDiff.lean:66`) ⇒ `Ξ.localInverse` is `ContDiffAt ℝ 1` at
   `Ξ(s₀,z₀) = (s₀, Φ_{s₀}z₀)`.  The global `(s,w)↦(s, Ψ_s w)` agrees with
   `Ξ.localInverse` on a nbhd
   (both left-inverses; `Ξ` injective on `Ioo 0 T ×ˢ univ` since `s` is preserved + each `Φ_s`
   injective per Step 2) ⇒ `ContDiffAt.congr` ⇒ `(s,w)↦(s,Ψ_s w)` is `ContDiffAt ℝ 1` at each point
   ⇒ `ContDiffOn ℝ 1` (projecting off the `s` component, `ContDiffAt.snd`).
4. **Bijectivity** is the per-slice `LeftInverse`/`RightInverse` from `exists_charFlow_inverse_On`,
   packaged into the `s`-indexed `Ψ`.
The two-time flow `Φ_{s→t} = Φ_t ∘ Ψ_s` is then jointly `C¹` by composing with `Φ_t` (`C¹` in its
argument, `#3`), and the dual core's transport identity differentiates it. -/
theorem charFlow_inverse_contDiffOn_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∃ Ψ : ℝ → PhaseSpace d → PhaseSpace d,
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2) (Set.Ioo 0 T ×ˢ Set.univ) := by
  classical
  obtain ⟨DΦ, hFDeriv, -⟩ := charFlow_hasFDerivAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hΦ_cda := charFlow_contDiffAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hstep2 := exists_charFlow_inverse_On gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hρD_cont hcontIcc
  have hbij : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.Bijective (fun z => ((charX s z, charV s z) : PhaseSpace d)) := by
    intro s hs
    obtain ⟨Ψ', e, _, hL', hR', _, _⟩ := hstep2 s hs
    exact ⟨hL'.injective, hR'.surjective⟩
  set Ψ : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => Function.invFun (fun z => (charX s z, charV s z)) with hΨ_def
  have hLeft : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)) :=
    fun s hs => Function.leftInverse_invFun (hbij s hs).1
  have hRight : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)) :=
    fun s hs => Function.rightInverse_invFun (hbij s hs).2
  refine ⟨Ψ, hLeft, hRight, ?_⟩
  set Ξ : ℝ × PhaseSpace d → ℝ × PhaseSpace d :=
    fun x => (x.1, (charX x.1 x.2, charV x.1 x.2)) with hΞ_def
  intro pt hpt
  obtain ⟨hs₀, -⟩ := hpt
  obtain ⟨Ψ', e, he_deriv, -, -, -, -⟩ := hstep2 pt.1 hs₀
  set z₀ : PhaseSpace d := Ψ pt.1 pt.2 with hz₀_def
  have hΦz₀ : (charX pt.1 z₀, charV pt.1 z₀) = pt.2 := hRight pt.1 hs₀ pt.2
  have hΞ_cda : ContDiffAt ℝ 1 Ξ (pt.1, z₀) :=
    contDiffAt_fst.prodMk (hΦ_cda (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩)
  set DΞ : (ℝ × PhaseSpace d) →L[ℝ] (ℝ × PhaseSpace d) :=
    (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).prod (DΦ (pt.1, z₀)) with hDΞ_def
  have hΞ_hd : HasFDerivAt Ξ DΞ (pt.1, z₀) :=
    (hasFDerivAt_fst).prodMk (hFDeriv (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩)
  have hincl : HasFDerivAt (fun z : PhaseSpace d => ((pt.1, z) : ℝ × PhaseSpace d))
      ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d))) z₀ :=
    (hasFDerivAt_const (pt.1 : ℝ) z₀).prodMk (hasFDerivAt_id z₀)
  have hslice : HasFDerivAt (fun z => (charX pt.1 z, charV pt.1 z))
      ((DΦ (pt.1, z₀)).comp
        ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d)))) z₀ :=
    (hFDeriv (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩).comp z₀ hincl
  have hcomp_eq : (DΦ (pt.1, z₀)).comp
      ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d)))
      = (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) :=
    hslice.unique (he_deriv z₀)
  have hslice_app : ∀ k : PhaseSpace d,
      DΦ (pt.1, z₀) ((0 : ℝ), k) = (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) k := by
    intro k
    have h1 : ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d))) k
        = ((0 : ℝ), k) := by simp
    rw [← h1, ← ContinuousLinearMap.comp_apply, hcomp_eq]
  have hker : LinearMap.ker (DΞ : (ℝ × PhaseSpace d) →ₗ[ℝ] (ℝ × PhaseSpace d)) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr (fun x hx => ?_)
    have hxapp : (x.1, DΦ (pt.1, z₀) x) = ((0 : ℝ), (0 : PhaseSpace d)) := by
      have : DΞ x = ((0 : ℝ), (0 : PhaseSpace d)) := hx
      simpa [hDΞ_def, ContinuousLinearMap.prod_apply] using this
    have hx1 : x.1 = 0 := (Prod.ext_iff.mp hxapp).1
    have hx2 : DΦ (pt.1, z₀) x = 0 := (Prod.ext_iff.mp hxapp).2
    have hxz : x = ((0 : ℝ), x.2) := Prod.ext hx1 rfl
    have hez : (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) x.2 = 0 := by
      rw [← hslice_app x.2, ← hxz]; exact hx2
    have : x.2 = 0 := by
      have hinj := (e z₀).injective
      have : (e z₀) x.2 = (e z₀) 0 := by rw [map_zero]; exact_mod_cast hez
      exact hinj this
    exact Prod.ext hx1 this
  have hrange : LinearMap.range (DΞ : (ℝ × PhaseSpace d) →ₗ[ℝ] (ℝ × PhaseSpace d)) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker))
  set eΞ : (ℝ × PhaseSpace d) ≃L[ℝ] (ℝ × PhaseSpace d) :=
    ContinuousLinearEquiv.ofBijective DΞ hker hrange with heΞ_def
  have hΞ_hd' : HasFDerivAt Ξ (eΞ : (ℝ × PhaseSpace d) →L[ℝ] (ℝ × PhaseSpace d)) (pt.1, z₀) :=
    hΞ_hd
  have hlocinv : ContDiffAt ℝ 1 (hΞ_cda.localInverse hΞ_hd' one_ne_zero) (Ξ (pt.1, z₀)) :=
    hΞ_cda.to_localInverse hΞ_hd' one_ne_zero
  have hstrict := hΞ_cda.hasStrictFDerivAt' hΞ_hd' (one_ne_zero)
  have hloc : ∀ᶠ x in 𝓝 ((pt.1, z₀) : ℝ × PhaseSpace d),
      ((fun y : ℝ × PhaseSpace d => ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d)) (Ξ x)) = x := by
    have hIoo : ∀ᶠ x in 𝓝 ((pt.1, z₀) : ℝ × PhaseSpace d), x.1 ∈ Set.Ioo (0 : ℝ) T :=
      continuous_fst.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hs₀)
    filter_upwards [hIoo] with x hx
    have hL2 : Ψ x.1 (charX x.1 x.2, charV x.1 x.2) = x.2 := hLeft x.1 hx x.2
    simp only [hΞ_def]
    rw [hL2]
  have huniq : ∀ᶠ y in 𝓝 (Ξ (pt.1, z₀)),
      ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d) = (hΞ_cda.localInverse hΞ_hd' one_ne_zero) y :=
    hstrict.localInverse_unique hloc
  have hΞeq : Ξ (pt.1, z₀) = (pt.1, pt.2) := by rw [hΞ_def]; exact Prod.ext rfl hΦz₀
  have hG_cda : ContDiffAt ℝ 1
      (fun y : ℝ × PhaseSpace d => ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d)) (pt.1, pt.2) := by
    rw [← hΞeq]
    exact hlocinv.congr_of_eventuallyEq huniq
  have hpt_eq : pt = (pt.1, pt.2) := rfl
  rw [hpt_eq]
  exact (hG_cda.snd).contDiffWithinAt

/-! ### Step 4 — the transported test function and the transport identity

The dual core's `s ↦ ∫ ψ_s d(f s)` argument rests on the backward-transported test
`ψ_s := φ ∘ Φ_{s→t}` where `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹` is the two-time flow (Step 3 gave it jointly
`C¹`).  Two deliverables, both taking the *outputs* of Step 3 (the inverse `Ψ` + the `C¹` terminal
map `Φ_t`) as hypotheses rather than re-deriving them from the flow-construction data: -/

omit [NeZero d] in
/-- **Step 4 (4a) — the two-time flow `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹` is jointly `C¹`** on
`Ioo 0 T ×ˢ univ`.

The two-time flow `(s,w) ↦ (charX t (Ψ_s w), charV t (Ψ_s w))` is the composition of the terminal
map `Φ_t = (charX t ·, charV t ·)` (`C¹` in its argument — `hΦt_C1`, from Step 2 / item (iii) at the
fixed time `t`) with the jointly-`C¹` inverse family `(s,w) ↦ Ψ_s w` (`hΨ_C1`, item (iv)).  Proof:
`ContDiff.comp_contDiffOn`. -/
theorem twoTimeFlow_contDiffOn_joint
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T t : ℝ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z))) :
    ContDiffOn ℝ 1
      (fun p : ℝ × PhaseSpace d => ((charX t (Ψ p.1 p.2), charV t (Ψ p.1 p.2)) : PhaseSpace d))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
  hΦt_C1.comp_contDiffOn hΨ_C1

omit [NeZero d] in
/-- **Step 4 (4b) — the transport identity `∂_s ψ_s + Dψ_s · b_s = 0`.**

For the backward-transported test `ψ_s(w) := φ(Φ_t(Ψ_s w)) = φ(Φ_{s→t} w)`, the partial
`s`-derivative cancels the spatial directional derivative along the field:
`∂_s ψ_s(w) = -(Dψ_s(w))(b_s(w))`, where `b_s = vlasovVectorField gradW ρ s` and
`Dψ_s(w) = fderiv ℝ (ψ s) w`.  This is the dual of `vlasov_traj_chain_rule` (the pushforward
direction) and the engine that makes `s ↦ ∫ ψ_s d(f s)` constant in Step 6.

Proof:
* `ψ` is jointly `C¹` on `Ioo 0 T ×ˢ univ` (4a + `φ` smooth), so `HasFDerivAt (uncurry ψ) Dψ (s,w)`
  at the interior point `(s,w)`, with `Dψ` the joint Fréchet derivative.
* Constancy curve: set `z₀ := Ψ_s w`, so `w = Φ_s z₀` (`hΨ_right`).  The composite
  `s' ↦ ψ_{s'}(Φ_{s'} z₀) = φ(Φ_t(Ψ_{s'}(Φ_{s'} z₀))) = φ(Φ_t z₀)` is **constant** in `s'`
  (`hΨ_left`: `Ψ_{s'} ∘ Φ_{s'} = id`), hence has zero `s'`-derivative.
* The curve `c(s') := (s', Φ_{s'} z₀)` has `HasDerivAt c (1, b_s w) s` (`hflow_ode` + `id`), with
  `c(s) = (s, w)`.  Chain rule: `0 = Dψ(s,w)(1, b_s w) = Dψ(s,w)(1,0) + Dψ(s,w)(0, b_s w)`.
* `Dψ(s,w)(1,0) = ∂_s ψ_s(w)` (compose `uncurry ψ` with `s' ↦ (s', w)`) and
  `Dψ(s,w)(0,k) = (fderiv ℝ (ψ s) w) k` (compose with `w' ↦ (s, w')`).  Surjectivity (`hΨ_right`)
  covers every `w`.  Rearrange to the claimed `HasDerivAt`. -/
theorem transportedTest_transport_identity
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T t : ℝ)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    (hflow_ode : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) (w : PhaseSpace d) :
    HasDerivAt (fun s' => φ (charX t (Ψ s' w), charV t (Ψ s' w)))
      (-(fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w
          (vlasovVectorField gradW ρ s w))) s := by
  classical
  -- uncurried two-time flow and transported test
  set G2 : ℝ × PhaseSpace d → PhaseSpace d :=
    fun p => (charX t (Ψ p.1 p.2), charV t (Ψ p.1 p.2)) with hG2_def
  set g : ℝ × PhaseSpace d → ℝ := fun p => φ (G2 p) with hg_def
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  have hmem : ((s, w) : ℝ × PhaseSpace d) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) :=
    ⟨hs, Set.mem_univ _⟩
  -- right-inverse identity: Φ_s (Ψ_s w) = w
  have hw : (charX s (Ψ s w), charV s (Ψ s w)) = w := hΨ_right s hs w
  -- g is jointly C¹, hence HasFDerivAt at the interior point (s,w)
  have hG2_cd : ContDiffOn ℝ 1 G2 (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    twoTimeFlow_contDiffOn_joint charX charV T t Ψ hΨ_C1 hΦt_C1
  have hG2_diff : DifferentiableAt ℝ G2 (s, w) :=
    hG2_cd.differentiableOn_one.differentiableAt (hopen.mem_nhds hmem)
  have hφ_diff : DifferentiableAt ℝ φ (G2 (s, w)) := hφ.differentiable (by simp) _
  have hg_fderiv : HasFDerivAt g (fderiv ℝ g (s, w)) (s, w) :=
    (hφ_diff.comp (s, w) hG2_diff).hasFDerivAt
  set G := fderiv ℝ g (s, w) with hG_def
  -- (A) spatial slice w' ↦ g (s, w') : fderiv = G ∘ inr
  have hslice_fderiv : HasFDerivAt (fun w' : PhaseSpace d => g (s, w'))
      (G.comp (ContinuousLinearMap.inr ℝ ℝ (PhaseSpace d))) w := by
    have := hg_fderiv.comp w (hasFDerivAt_prodMk_right s w)
    simpa only [Function.comp_def] using this
  -- (B) ∂_s slice s' ↦ g (s', w) : HasDerivAt with value G (1, 0)
  have hscurve : HasDerivAt (fun s' => ((s', w) : ℝ × PhaseSpace d))
      ((1 : ℝ), (0 : PhaseSpace d)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s w)
  have hs_slice : HasDerivAt (fun s' => g (s', w)) (G ((1 : ℝ), (0 : PhaseSpace d))) s := by
    have := hg_fderiv.comp_hasDerivAt s hscurve
    simpa only [Function.comp_def] using this
  -- (C) constancy curve c(s') = (s', Φ_{s'} (Ψ_s w)); chain rule gives G(1, b)
  have hccurve : HasDerivAt
      (fun s' => ((s', (charX s' (Ψ s w), charV s' (Ψ s w))) : ℝ × PhaseSpace d))
      ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) s :=
    (hasDerivAt_id s).prodMk (hflow_ode (Ψ s w) s hs)
  have hcs : ((s, (charX s (Ψ s w), charV s (Ψ s w))) : ℝ × PhaseSpace d) = (s, w) := by rw [hw]
  have hgc : HasDerivAt (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w))))
      (G ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))) s := by
    have hF := hg_fderiv
    rw [← hcs] at hF
    have := hF.comp_hasDerivAt s hccurve
    simpa only [Function.comp_def] using this
  -- (D) the composite is eventually constant near s, so its derivative is 0
  have hconst : (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w)))) =ᶠ[nhds s]
      (fun _ => φ (charX t (Ψ s w), charV t (Ψ s w))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs'
    simp only [hg_def, hG2_def]
    rw [hΨ_left s' hs' (Ψ s w)]
  have hgc0 : HasDerivAt (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w)))) 0 s :=
    (hasDerivAt_const s (φ (charX t (Ψ s w), charV t (Ψ s w)))).congr_of_eventuallyEq hconst
  -- (E) uniqueness: G (1, b) = 0
  have hGzero : G ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) = 0 :=
    hgc.unique hgc0
  -- (F) split G(1,b) = G(1,0) + G(0,b); identify G(0,b) with the target fderiv applied to b
  have hsplit : ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))
      = ((1 : ℝ), (0 : PhaseSpace d))
        + ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) := by
    ext <;> simp
  have hb_eq : vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))
      = vlasovVectorField gradW ρ s w := by rw [hw]
  have hG0b : G ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))
      = (fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w)
          (vlasovVectorField gradW ρ s w) := by
    have hfd : fderiv ℝ (fun w' : PhaseSpace d => g (s, w')) w
        = G.comp (ContinuousLinearMap.inr ℝ ℝ (PhaseSpace d)) := hslice_fderiv.fderiv
    have hfun : (fun w' : PhaseSpace d => g (s, w'))
        = (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) := rfl
    rw [hfun] at hfd
    rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hb_eq]
  -- (G) G(1,0) = -(target fderiv)(b)
  have hval : G ((1 : ℝ), (0 : PhaseSpace d))
      = -(fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w)
          (vlasovVectorField gradW ρ s w) := by
    have hsum : G ((1 : ℝ), (0 : PhaseSpace d))
        + G ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) = 0 := by
      rw [← map_add, ← hsplit]; exact hGzero
    rw [hG0b] at hsum
    linarith [hsum]
  -- (H) conclude
  have hgoalfun : (fun s' => φ (charX t (Ψ s' w), charV t (Ψ s' w)))
      = (fun s' => g (s', w)) := rfl
  rw [hgoalfun, ← hval]
  exact hs_slice


end Vlasov
