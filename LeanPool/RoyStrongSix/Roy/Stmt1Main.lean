/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Roy.Stmt1

/-!
# Roy's Theorem 1bis: Theorem 1 ⇒ Statement 1 for the subquotient system
-/

@[expose] public section

namespace LeanPool

open Module Submodule

noncomputable section

namespace StrongSix.Roy.Amb

variable {M : Amb}

/-- Kernels of block maps intersect product subspaces componentwise. -/
theorem ker_prodMap_inf {d0 d1 k0 k1 : ℕ}
    (ψ0 : (Fin d0 → ℂ) →ₗ[ℂ] (Fin k0 → ℂ))
    (ψ1 : (Fin d1 → ℂ) →ₗ[ℂ] (Fin k1 → ℂ))
    (S0 T0 : Submodule ℂ (Fin d0 → ℂ)) (S1 T1 : Submodule ℂ (Fin d1 → ℂ))
    (h0 : LinearMap.ker ψ0 ⊓ T0 = S0) (h1 : LinearMap.ker ψ1 ⊓ T1 = S1) :
    LinearMap.ker (LinearMap.prodMap ψ0 ψ1) ⊓ T0.prod T1 = S0.prod S1 := by
  ext ⟨x0, x1⟩
  have e0 := congrArg (x0 ∈ ·) h0
  have e1 := congrArg (x1 ∈ ·) h1
  simp only [Submodule.mem_inf, LinearMap.mem_ker, eq_iff_iff] at e0 e1
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.prodMap_apply,
    Prod.mk_eq_zero, Submodule.mem_prod]
  tauto

/-- **Roy's Theorem 1bis**: Waldschmidt's Theorem 1 implies Statement 1 for the subquotient system
of an ambient `(E, Y, W, V)` with `Y ⊆ Qbar^{d₀} × 𝓛^{d₁}` and `W` rational over `Qbar`. -/
theorem stmt1_of_theorem1 (hT1 : WaldschmidtTheorem1)
    (hYalg : ∀ p ∈ M.Y, AlgVec p.1 ∧ ∀ j, p.2 j ∈ logAlg) (hW : RationalOverQbar M.W) :
    Stmt1 M.sys a b c d := by
  intro X hbX
  have hY := M.hYfin
  -- realization of the two factors
  obtain ⟨k0, ψ0, P0, hmap0, hker0, htop0⟩ := realize_factor X.1.1.h0 X.1.2.h0 X.2.1
  obtain ⟨k1, ψ1, P1, hmap1, hker1, htop1⟩ := realize_factor X.1.1.h1 X.1.2.h1 X.2.2
  let ψ : E M.d0 M.d1 →ₗ[ℂ] E k0 k1 := LinearMap.prodMap ψ0 ψ1
  have hψ : ∀ x, ψ x = (ψ0 x.1, ψ1 x.2) := fun x => rfl
  have hψ0 : ∀ v : Fin M.d1 → ℂ, (ψ (0, v)).1 = 0 := fun v => by rw [hψ]; exact map_zero ψ0
  have hkerψ : LinearMap.ker ψ ⊓ X.1.2.sub = X.1.1.sub :=
    ker_prodMap_inf ψ0 ψ1 _ _ _ _ hker0 hker1
  have htopψ : X.1.2.sub.map ψ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y0, y1⟩ -
    have h0 : y0 ∈ X.1.2.S0.map ψ0 := by rw [htop0]; trivial
    have h1 : y1 ∈ X.1.2.S1.map ψ1 := by rw [htop1]; trivial
    obtain ⟨x0, hx0, rfl⟩ := h0
    obtain ⟨x1, hx1, rfl⟩ := h1
    exact ⟨(x0, x1), ⟨hx0, hx1⟩, rfl⟩
  have hΩψ : (Omega M.d0 M.d1 ⊓ subQ X.1.2).map (ψ.restrictScalars ℚ) = Omega k0 k1 := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨hxΩ, -⟩, rfl⟩
      rw [Omega_eq_map] at hxΩ
      obtain ⟨q, hq, rfl⟩ := hxΩ
      rw [Omega_eq_map]
      exact ⟨ψ1 q, P1 q hq, (μ_block ψ ψ1 hψ0 (fun x => rfl) q).symm⟩
    · intro z hz
      rw [Omega_eq_map] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      rw [← hmap1] at hp
      obtain ⟨q, ⟨hqT, hqF⟩, rfl⟩ := hp
      refine ⟨μ M.d0 M.d1 q, ⟨?_, ?_⟩, μ_block ψ ψ1 hψ0 (fun x => rfl) q⟩
      · rw [Omega_eq_map]; exact mem_map_of_mem hqF
      · change μ M.d0 M.d1 q ∈ X.1.2.sub
        rw [μ_apply]; exact ⟨X.1.2.S0.zero_mem, X.1.2.S1.smul_mem ω hqT⟩
  obtain ⟨hr, hd1, hvd, hwd, hc, he⟩ :=
    transport X ψ ψ1 (fun x => rfl) hkerψ htopψ hker1 htop1 hΩψ
  -- the coordinate object
  set Y' : Submodule ℚ (E k0 k1) := (M.Y ⊓ subQ X.1.2).map (ψ.restrictScalars ℚ) with hY'
  set W' : Submodule ℂ (E k0 k1) := (M.W ⊓ X.1.2.sub).map ψ with hW'
  set V' : Submodule ℂ (E k0 k1) := (M.V ⊓ X.1.2.sub).map ψ with hV'
  have hY'fin : FiniteDimensional ℚ Y' := Module.Finite.map _ _
  have halgψ : ∀ u : E M.d0 M.d1, AlgVec u.1 → AlgVec u.2 →
      AlgVec (ψ u).1 ∧ AlgVec (ψ u).2 := fun u h1 h2 =>
    ⟨algVec_iff.mpr (P0 _ (algVec_iff.mp h1)), fun j => presQ_preserves ψ1 P1 algSub h2 j⟩
  have hY'alg : ∀ p ∈ Y', AlgVec p.1 ∧ ∀ j, p.2 j ∈ logAlg := by
    rintro _ ⟨y, ⟨hyY, -⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hYalg y hyY
    exact ⟨algVec_iff.mpr (P0 _ (algVec_iff.mp h1)),
      fun j => presQ_preserves ψ1 P1 logAlgSub h2 j⟩
  have hTrat : RationalOverQbar X.1.2.sub := rationalOverQbar_prod X.1.2.h0 X.1.2.h1
  have hW'rat : RationalOverQbar W' :=
    rationalOverQbar_map ψ halgψ (rationalOverQbar_inf hW hTrat)
  have hYV' : ∀ p ∈ Y', p ∈ V' := by
    rintro _ ⟨y, ⟨hyY, hyT⟩, rfl⟩
    exact mem_map_of_mem ⟨M.hYV y hyY, hyT⟩
  have hWV' : W' ≤ V' := map_mono (inf_le_inf_right _ M.hWV)
  have hvdr := vd_le_r X
  have hV'top : V' ≠ ⊤ := by
    intro h
    have h1 : finrank ℂ V' = k0 + k1 := by rw [h, finrank_top, finrank_E]
    have : b X = 0 := by unfold b; omega
    exact hbX this
  obtain ⟨d0', d1', s, hsurj, hs0, hs1, hWs, hineq⟩ :=
    hT1 k0 k1 Y' W' V' hY'fin hY'alg hW'rat hYV' hWV' hV'top
  -- block decomposition of `s`
  have hsnd0 : ∀ u : Fin k0 → ℂ, (s (u, 0)).2 = 0 := by
    let L := (LinearMap.snd ℂ (Fin d0' → ℂ) (Fin d1' → ℂ)).comp (s.comp (LinearMap.inl ℂ _ _))
    have hL : L = 0 := linmap_eq_zero_of_single L fun i => by
      obtain ⟨u', -, hu'⟩ := hs0 (Pi.single i 1) (algVec_iff.mpr (single_mem_Fpts i))
      change (s (Pi.single i 1, 0)).2 = 0
      rw [hu']
    intro u
    exact LinearMap.congr_fun hL u
  have hfst1 : ∀ v : Fin k1 → ℂ, (s (0, v)).1 = 0 := by
    let L := (LinearMap.fst ℂ (Fin d0' → ℂ) (Fin d1' → ℂ)).comp (s.comp (LinearMap.inr ℂ _ _))
    have hL : L = 0 := linmap_eq_zero_of_single L fun i => by
      obtain ⟨v', -, hv'⟩ := hs1 (Pi.single i 1) (ratVec_iff.mpr (single_mem_Fpts i))
      change (s (0, Pi.single i 1)).1 = 0
      rw [hv']
    intro v
    exact LinearMap.congr_fun hL v
  let s0 := (LinearMap.fst ℂ (Fin d0' → ℂ) (Fin d1' → ℂ)).comp (s.comp (LinearMap.inl ℂ _ _))
  let s1 := (LinearMap.snd ℂ (Fin d0' → ℂ) (Fin d1' → ℂ)).comp (s.comp (LinearMap.inr ℂ _ _))
  have hsplit : ∀ x, s x = (s0 x.1, s1 x.2) := by
    intro x
    have hx : x = (x.1, 0) + (0, x.2) := by simp
    have e := congrArg s hx
    rw [map_add] at e
    rw [e]
    refine Prod.ext ?_ ?_
    · change (s (x.1, 0)).1 + (s (0, x.2)).1 = (s (x.1, 0)).1
      rw [hfst1, add_zero]
    · change (s (x.1, 0)).2 + (s (0, x.2)).2 = (s (0, x.2)).2
      rw [hsnd0, zero_add]
  have P0s : PresF Qb s0 := by
    intro u hu
    obtain ⟨u', hu', he'⟩ := hs0 u (algVec_iff.mpr hu)
    change (s (u, 0)).1 ∈ Fpts Qb (Fin d0')
    rw [he']; exact algVec_iff.mp hu'
  have P1s : PresF ℚ s1 := by
    intro v hv
    obtain ⟨v', hv', he'⟩ := hs1 v (ratVec_iff.mpr hv)
    change (s (0, v)).2 ∈ Fpts ℚ (Fin d1')
    rw [he']; exact ratVec_iff.mp hv'
  have hs1surj : Function.Surjective s1 := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (0, y)
    refine ⟨x.2, ?_⟩
    have := congrArg Prod.snd hx
    rw [hsplit] at this
    exact this
  -- the composite and the new object
  let σ0 := s0.comp ψ0
  let σ1 := s1.comp ψ1
  let σ := s.comp ψ
  have hσ : ∀ x, σ x = (σ0 x.1, σ1 x.2) := fun x => by
    change s (ψ x) = _; rw [hsplit, hψ]; rfl
  obtain ⟨AK0, hAK0, hK0⟩ := isRat_ker σ0 (fun x hx => P0s _ (P0 x hx))
  obtain ⟨AK1, hAK1, hK1⟩ := isRat_ker σ1 (fun x hx => P1s _ (P1 x hx))
  have hrat0 : IsRat Qb (X.1.2.S0 ⊓ LinearMap.ker σ0) := by
    have hA : ptsOf Qb X.1.2.S0 ≤ Fpts Qb (Fin M.d0) := inf_le_right
    refine ⟨ptsOf Qb X.1.2.S0 ⊓ AK0, inf_le_left.trans hA, ?_⟩
    rw [← span_inf_span_of_le_Fpts _ _ hA hAK0, ← hK0, ← span_ptsOf X.1.2.h0]
  have hrat1 : IsRat ℚ (X.1.2.S1 ⊓ LinearMap.ker σ1) := by
    have hA : ptsOf ℚ X.1.2.S1 ≤ Fpts ℚ (Fin M.d1) := inf_le_right
    refine ⟨ptsOf ℚ X.1.2.S1 ⊓ AK1, inf_le_left.trans hA, ?_⟩
    rw [← span_inf_span_of_le_Fpts _ _ hA hAK1, ← hK1, ← span_ptsOf X.1.2.h1]
  let S'' : RSub M.d0 M.d1 :=
    ⟨X.1.2.S0 ⊓ LinearMap.ker σ0, X.1.2.S1 ⊓ LinearMap.ker σ1, hrat0, hrat1⟩
  let X'' : M.Ob := ⟨(S'', X.1.2), ⟨inf_le_left, inf_le_left⟩⟩
  have hS0 : X.1.1.S0 ≤ S''.S0 := by
    intro x hx
    have h : x ∈ LinearMap.ker ψ0 ⊓ X.1.2.S0 := by rw [hker0]; exact hx
    refine ⟨X.2.1 hx, ?_⟩
    change s0 (ψ0 x) = 0
    rw [LinearMap.mem_ker.mp h.1, map_zero]
  have hS1 : X.1.1.S1 ≤ S''.S1 := by
    intro x hx
    have h : x ∈ LinearMap.ker ψ1 ⊓ X.1.2.S1 := by rw [hker1]; exact hx
    refine ⟨X.2.2 hx, ?_⟩
    change s1 (ψ1 x) = 0
    rw [LinearMap.mem_ker.mp h.1, map_zero]
  have hCok : M.sys.Cok X X'' := ⟨rfl, ⟨hS0, hS1⟩⟩
  have hkerσ : LinearMap.ker σ ⊓ X''.1.2.sub = X''.1.1.sub := by
    ext ⟨x0, x1⟩
    simp only [Submodule.mem_inf, LinearMap.mem_ker, hσ, Prod.mk_eq_zero, RSub.sub,
      Submodule.mem_prod, X'', S'']
    tauto
  have htopσ : X''.1.2.sub.map σ = ⊤ := by
    change X.1.2.sub.map (s.comp ψ) = ⊤
    rw [Submodule.map_comp, htopψ, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  have hkerσ1 : LinearMap.ker σ1 ⊓ X''.1.2.S1 = X''.1.1.S1 := inf_comm _ _
  have htopσ1 : X''.1.2.S1.map σ1 = ⊤ := by
    change X.1.2.S1.map (s1.comp ψ1) = ⊤
    rw [Submodule.map_comp, htop1, Submodule.map_top, LinearMap.range_eq_top.mpr hs1surj]
  have hΩσ : (Omega M.d0 M.d1 ⊓ subQ X''.1.2).map (σ.restrictScalars ℚ) = Omega d0' d1' := by
    change (Omega M.d0 M.d1 ⊓ subQ X.1.2).map
      ((s.restrictScalars ℚ).comp (ψ.restrictScalars ℚ)) = _
    rw [Submodule.map_comp, hΩψ]
    exact map_Omega_of_block s s1 hfst1 (fun x => by rw [hsplit]) P1s hs1surj
  obtain ⟨hr'', hd1'', hvd'', hwd'', hc'', he''⟩ :=
    transport X'' σ σ1 (fun x => by rw [hσ]) hkerσ htopσ hkerσ1 htopσ1 hΩσ
  -- identify the transported quantities with those of Theorem 1
  have eW : (M.W ⊓ X''.1.2.sub).map σ = W'.map s := Submodule.map_comp _ _ _
  have eY : (M.Y ⊓ subQ X''.1.2).map (σ.restrictScalars ℚ) = Y'.map (s.restrictScalars ℚ) := by
    change (M.Y ⊓ subQ X.1.2).map ((s.restrictScalars ℚ).comp (ψ.restrictScalars ℚ)) = _
    exact Submodule.map_comp _ _ _
  rw [eW] at hwd''
  rw [eY] at hc'' he''
  -- inequalities needed for the casts
  have h1 := e_le_d1f X
  have h2 := e_le_d1f X''
  have h3 := vd_le_r X''
  have h4 := wd_le_vd X''
  have hbd : b X'' + d X'' = r X'' - wd X'' := by unfold b d; omega
  have hWlt : finrank ℂ ↥(W'.map s) < d0' + d1' := by
    have := Submodule.finrank_lt hWs
    rwa [finrank_E] at this
  refine ⟨X'', hCok, by omega, ?_⟩
  -- the inequality
  have h2' : finrank ℚ ↥(Y'.map (s.restrictScalars ℚ) ⊓ Omega d0' d1') ≤ d1' := by
    rw [← he'', ← hd1'']; exact h2
  have h1' : finrank ℚ ↥(Y' ⊓ Omega k0 k1) ≤ k1 := by rw [← he, ← hd1]; exact h1
  have hv' : finrank ℂ ↥V' ≤ k0 + k1 := by rw [← hvd, ← hr]; exact hvdr
  have hL : ((a X'' + c X'' : ℕ) : ℚ) / (b X'' + d X'' : ℕ) =
      ((d1' : ℚ) - finrank ℚ ↥(Y'.map (s.restrictScalars ℚ) ⊓ Omega d0' d1') +
          finrank ℚ ↥(Y'.map (s.restrictScalars ℚ))) /
        ((d0' + d1' : ℚ) - finrank ℂ ↥(W'.map s)) := by
    rw [hbd]
    unfold a
    rw [hd1'', he'', hc'', hwd'', hr'']
    push_cast [Nat.cast_sub h2', Nat.cast_sub hWlt.le]
    ring
  have hR : (a X : ℚ) / b X =
      ((k1 : ℚ) - finrank ℚ ↥(Y' ⊓ Omega k0 k1)) / ((k0 + k1 : ℚ) - finrank ℂ ↥V') := by
    unfold a b
    rw [hd1, he, hvd, hr]
    push_cast [Nat.cast_sub h1', Nat.cast_sub hv']
    ring
  rw [hL, hR]
  exact hineq

end StrongSix.Roy.Amb

end

end LeanPool
