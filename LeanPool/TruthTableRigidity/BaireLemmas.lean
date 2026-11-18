/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import LeanPool.TruthTableRigidity.BaireTopology

/-!
# Lemmas 4.1 and 4.2: uniform relations on a comeager set, and a splitting bit
-/

@[expose] public section

open Filter Topology

namespace TT

open OAI.TuringRigidity

/-! ### Non-constancy on comeager sets (property (N)) -/

/-- If `F` induces an automorphism, then `F` is not constant on `D ∩ N_α` for any comeager `D`. -/
theorem InducedBy.nonconst_residual {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hπ : InducedBy π F) {D : Set Oracle} (hD : D ∈ residual Oracle) (α : List Bool) :
    ∃ Z ∈ D, Z ∈ Ncyl α ∧ ∃ Z' ∈ D, Z' ∈ Ncyl α ∧ F Z ≠ F Z' := by
  have hdense : ∀ D' ∈ residual Oracle, ∃ Z ∈ D', Z ∈ Ncyl α := fun D' hD' => by
    obtain ⟨Z, hZ1, hZ2⟩ := (dense_of_mem_residual hD').inter_open_nonempty (Ncyl α)
      (isOpen_Ncyl α) ⟨prep α zzero, prep_mem _ _⟩
    exact ⟨Z, hZ2, hZ1⟩
  obtain ⟨A₀, hA₀D, hA₀α⟩ := hdense D hD
  by_contra hcon
  push Not at hcon
  have hsub : ∀ Z ∈ D, Z ∈ Ncyl α → TTReducible Z A₀ := by
    intro Z hZD hZα
    have h1 : ttDegree Z = ttDegree A₀ := by
      apply π.injective
      rw [← hπ, ← hπ, hcon Z hZD hZα A₀ hA₀D hA₀α]
    exact (ttDegree_eq_iff.mp h1).1
  obtain ⟨Z, ⟨hZD, hZS⟩, hZα⟩ := hdense _ (diff_countable_mem_residual hD (countable_ttReducible
    A₀))
  exact hZS (hsub Z hZD hZα)

/-! ### A global-map variant of Lemma 4.1 -/

/-- **Global-map variant of Lemma 4.1.** Let `F` satisfy (M) and (J′) and be continuous
on a dense `Gδ` set `D`.
Then there are strings `α, β` of the same length and tt-functionals `Φ+, Φ−, Φ1/2` such that
comeager many pairs in `N_α × N_β` satisfy the relations `(R+)`, `(R−)`, `(R1/2)` and have
first coordinate in `D`. This formulation takes global monotonicity and join reductions. -/
theorem lemma_4_1 {F : Oracle → Oracle} {D : Set Oracle} (hDG : IsGδ D) (hDd : Dense D)
    (hFD : ContinuousOn F D) (hmono : ∀ A B, TTReducible A B → TTReducible (F A) (F B))
    (hjoin : ∀ A B, TTReducible (F (ojoin A B)) (ojoin (F A) (F B))) :
    ∃ α β : List Bool, α.length = β.length ∧
      ∃ Φp Φm Φh : Oracle → Oracle, IsTTFunctional Φp ∧ IsTTFunctional Φm ∧
        IsTTFunctional Φh ∧ ∀ᶠ p in residual (Oracle × Oracle),
          p.1 ∈ Ncyl α → p.2 ∈ Ncyl β → Relations F Φp Φm Φh p.1 p.2 ∧ p.1 ∈ D := by
  have hDres : D ∈ residual Oracle := mem_residual.mpr ⟨D, subset_rfl, hDG, hDd⟩
  have cid : Continuous (id : Oracle → Oracle) := continuous_id
  have cdbl : Continuous fun H : Oracle => zaddO H H :=
    continuous_zaddO.comp₂ cid cid
  let fA : Oracle × Oracle → Oracle := fun p => zaddO p.1 p.2
  let fN : Oracle × Oracle → Oracle := fun p => znegO p.2
  let fD : Oracle × Oracle → Oracle := fun p => zaddO p.1 (zaddO p.2 p.2)
  have cA : Continuous fA := continuous_zaddO
  have cN : Continuous fN := continuous_znegO.comp continuous_snd
  have cD : Continuous fD := continuous_zaddO.comp₂ continuous_fst (cdbl.comp' continuous_snd)
  let E₀ : Set (Oracle × Oracle) :=
    Prod.fst ⁻¹' D ∩ Prod.snd ⁻¹' D ∩ fA ⁻¹' D ∩ fN ⁻¹' D ∩ fD ⁻¹' D
  have hE₀G : IsGδ E₀ :=
    ((((IsGδ.preimage continuous_fst hDG).inter (IsGδ.preimage continuous_snd hDG)).inter
      (IsGδ.preimage cA hDG)).inter (IsGδ.preimage cN hDG)).inter (IsGδ.preimage cD hDG)
  have r1 : Prod.fst ⁻¹' D ∈ residual (Oracle × Oracle) :=
    preimage_mem_residual continuous_fst isOpenMap_fst hDres
  have r2 : Prod.snd ⁻¹' D ∈ residual (Oracle × Oracle) :=
    preimage_mem_residual continuous_snd isOpenMap_snd hDres
  have r3 : fA ⁻¹' D ∈ residual (Oracle × Oracle) :=
    preimage_mem_residual cA (isOpenMap_shear_fst id continuous_id) hDres
  have r4 : fN ⁻¹' D ∈ residual (Oracle × Oracle) :=
    preimage_mem_residual cN (negHomeo.isOpenMap.comp isOpenMap_snd) hDres
  have r5 : fD ⁻¹' D ∈ residual (Oracle × Oracle) :=
    preimage_mem_residual cD (isOpenMap_shear_fst (fun H => zaddO H H) cdbl) hDres
  have hE₀res : E₀ ∈ residual (Oracle × Oracle) :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem r1 r2) r3) r4) r5
  have hE₀d : Dense E₀ := dense_of_mem_residual hE₀res
  have cF1 : ContinuousOn (fun p : Oracle × Oracle => F p.1) E₀ :=
    hFD.comp continuous_fst.continuousOn fun p hp => hp.1.1.1.1
  have cF2 : ContinuousOn (fun p : Oracle × Oracle => F p.2) E₀ :=
    hFD.comp continuous_snd.continuousOn fun p hp => hp.1.1.1.2
  have cFA : ContinuousOn (fun p : Oracle × Oracle => F (fA p)) E₀ :=
    hFD.comp cA.continuousOn fun p hp => hp.1.1.2
  have cFN : ContinuousOn (fun p : Oracle × Oracle => F (fN p)) E₀ :=
    hFD.comp cN.continuousOn fun p hp => hp.1.2
  have cFD : ContinuousOn (fun p : Oracle × Oracle => F (fD p)) E₀ :=
    hFD.comp cD.continuousOn fun p hp => hp.2
  obtain ⟨V₃, -, hV₃, hV₃ne, Φp, Φm, Φh, hp, hm, hh, hR⟩ :=
    uniformize_relations hE₀G hE₀d isOpen_univ Set.univ_nonempty cF1 cF2 cFA cFN cFD
      hmono hjoin
  obtain ⟨⟨x, y⟩, hxy⟩ := hV₃ne
  obtain ⟨k, hk⟩ := exists_cyl_prod_subset hV₃ hxy
  refine ⟨pre x k, pre y k, by simp [length_pre], Φp, Φm, Φh, hp, hm, hh, ?_⟩
  filter_upwards [hE₀res] with p hpE h1 h2
  rw [mem_Ncyl_pre] at h1 h2
  have h3 : p ∈ V₃ := hk ⟨h1, h2⟩
  refine ⟨hR p hpE h3, hpE.1.1.1.1⟩

/-! ### The nonconstancy form of Lemma 4.2 -/

/-- A function continuous on `D` has locally constant bits on `D`. -/
theorem locally_const_bit {F : Oracle → Oracle} {D : Set Oracle}
    (hFD : ContinuousOn F D) {Z₀ : Oracle} (hZ₀ : Z₀ ∈ D) (j : ℕ) :
    ∃ k, ∀ Z ∈ D, Z ∈ cyl Z₀ k → F Z j = F Z₀ j := by
  have hf : ContinuousWithinAt (fun Z => F Z j) D Z₀ :=
    (continuous_apply j).continuousAt.comp_continuousWithinAt (hFD Z₀ hZ₀)
  have hev := hf.eventually ((isOpen_discrete {F Z₀ j}).mem_nhds rfl)
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at hev
  obtain ⟨t, ht, hto, hZ₀t⟩ := hev
  obtain ⟨k, hk⟩ := exists_cyl_subset hto hZ₀t
  exact ⟨k, fun Z hZD hZ => ht Z (hk hZ) hZD⟩

/-- **Nonconstancy form of Lemma 4.2.** A splitting bit for a function continuous on `D`
and nonconstant on `D ∩ N_α`. -/
theorem lemma_4_2 {F : Oracle → Oracle} {D : Set Oracle} (hFD : ContinuousOn F D)
    {α : List Bool} (hnc : ∃ Z ∈ D, Z ∈ Ncyl α ∧ ∃ Z' ∈ D, Z' ∈ Ncyl α ∧ F Z ≠ F Z') :
    ∃ (j : ℕ) (b i : Bool) (σ q₁ : List Bool), α <+: σ ∧ σ ++ [!i] <+: q₁ ∧
      (∀ Z ∈ D, Z ∈ Ncyl (σ ++ [i]) → F Z j = b) ∧ (∀ Z ∈ D, Z ∈ Ncyl q₁ → F Z j = !b) := by
  obtain ⟨Z₀, hZ₀D, hZ₀α, Z', hZ'D, hZ'α, hne⟩ := hnc
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  let Dec : List Bool → Prop := fun ν =>
    ∀ Z ∈ D, Z ∈ Ncyl ν → ∀ Z' ∈ D, Z' ∈ Ncyl ν → F Z j = F Z' j
  have hDecα : ¬ Dec α := fun h => hj (h Z₀ hZ₀D hZ₀α Z' hZ'D hZ'α)
  have hαeq : pre Z₀ α.length = α := hZ₀α
  obtain ⟨k₀, hk₀⟩ := locally_const_bit hFD hZ₀D j
  have hex : ∃ n, Dec (pre Z₀ n) := by
    refine ⟨k₀, fun Z hZ h1 Z'' hZ'' h2 => ?_⟩
    rw [mem_Ncyl_pre] at h1 h2
    rw [hk₀ Z hZ h1, hk₀ Z'' hZ'' h2]
  classical
  let n₀ := Nat.find hex
  have hn₀ : Dec (pre Z₀ n₀) := Nat.find_spec hex
  have hmin : ∀ n < n₀, ¬ Dec (pre Z₀ n) := fun n hn => Nat.find_min hex hn
  have hgt : α.length < n₀ := by
    by_contra hle
    push Not at hle
    apply hDecα
    intro Z hZ h1 Z'' hZ'' h2
    have hsub : Ncyl α ⊆ Ncyl (pre Z₀ n₀) := by
      apply Ncyl_antitone
      rw [← hαeq]; exact pre_prefix Z₀ hle
    exact hn₀ Z hZ (hsub h1) Z'' hZ'' (hsub h2)
  obtain ⟨l, hl⟩ : ∃ l, n₀ = l + 1 := ⟨n₀ - 1, by omega⟩
  have hαl : α.length ≤ l := by omega
  set σ := pre Z₀ l
  set i := Z₀ l
  have hq₀ : pre Z₀ (l + 1) = σ ++ [i] := pre_succ Z₀ l
  have hDecq₀ : Dec (σ ++ [i]) := by rw [← hq₀, ← hl]; exact hn₀
  have hσ : ¬ Dec σ := hmin l (by omega)
  have hZ₀q₀ : Z₀ ∈ Ncyl (σ ++ [i]) := by rw [← hq₀, mem_Ncyl_pre]; exact mem_cyl _ _
  set b := F Z₀ j
  have hb0 : ∀ Z ∈ D, Z ∈ Ncyl (σ ++ [i]) → F Z j = b := fun Z hZ h =>
    hDecq₀ Z hZ h Z₀ hZ₀D hZ₀q₀
  -- a point of `D ∩ N_σ` with the other value
  obtain ⟨Z₁, hZ₁D, hZ₁σ, hZ₁b⟩ : ∃ Z₁ ∈ D, Z₁ ∈ Ncyl σ ∧ F Z₁ j = !b := by
    by_contra hcon
    push Not at hcon
    apply hσ
    intro Z hZ h1 Z'' hZ'' h2
    have e1 : F Z j = b := by
      have := hcon Z hZ h1; revert this; cases F Z j <;> cases b <;> simp
    have e2 : F Z'' j = b := by
      have := hcon Z'' hZ'' h2; revert this; cases F Z'' j <;> cases b <;> simp
    rw [e1, e2]
  have hZ₁l : Z₁ l = !i := by
    by_contra hcon
    have hZ₁i : Z₁ l = i := by revert hcon; cases Z₁ l <;> cases i <;> simp
    have hmem : Z₁ ∈ Ncyl (σ ++ [i]) := by
      rw [Ncyl, Set.mem_ofPred_eq, List.length_append, List.length_singleton]
      have : pre Z₁ l = σ := by
        have h := hZ₁σ; rw [Ncyl, Set.mem_ofPred_eq] at h
        rwa [show σ.length = l from length_pre Z₀ l] at h
      rw [pre_succ, show σ.length = l from length_pre Z₀ l, this, hZ₁i]
    have := hb0 Z₁ hZ₁D hmem
    rw [hZ₁b] at this
    cases b <;> simp at this
  have hZ₁pre : pre Z₁ (l + 1) = σ ++ [!i] := by
    rw [pre_succ, hZ₁l]
    have h := hZ₁σ; rw [Ncyl, Set.mem_ofPred_eq] at h
    rw [show σ.length = l from length_pre Z₀ l] at h; rw [h]
  obtain ⟨k₁, hk₁⟩ := locally_const_bit hFD hZ₁D j
  refine ⟨j, b, i, σ, pre Z₁ (max k₁ (l + 1)), ?_, ?_, hb0, ?_⟩
  · rw [← hαeq]; exact pre_prefix Z₀ hαl
  · rw [← hZ₁pre]; exact pre_prefix Z₁ (le_max_right _ _)
  · intro Z hZD hZ
    rw [mem_Ncyl_pre] at hZ
    rw [hk₁ Z hZD (cyl_antitone Z₁ (le_max_left _ _) hZ), hZ₁b]

end TT
