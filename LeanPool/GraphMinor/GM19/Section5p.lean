/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5o
public import LeanPool.GraphMinor.GM19.Theta

/-!
# The circuit of the proof of (5.5)

Take a non-null-homotopic circuit `F` of `Γ*` with `½|E(F)| ≤ n`, and with `|V(F) ∩ Σ|` as small as
possible. The paper
says that then "for each pole $r^*$, $V(F)$ contains at most two neighbours of $r^*$, and at most
one if $r^* \notin V(F_i)$". This
comes from the three-path lemma `null_of_theta`: a path through `r*` between two vertices of `F`
gives a circuit with fewer
vertices in `Σ`, and it is non-null-homotopic for one of the two ways of closing it.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}


/-- The circuits among which `F` is chosen in the proof of (5.5). -/
def IsShortCircuit (rad : RadialDrawing cap Γ) (n : ℕ) (F : Drawing Shat) : Prop :=
  F.IsCircuitOf rad.G ∧ ¬ IsNullHomotopicOArc F.U ∧ F.E.ncard / 2 ≤ n

/-- A chord of a circuit: one of the two ways of closing it gives a circuit that is not
null-homotopic. -/
theorem exists_closing (hT : IsClosedSurface Shat) [ConnectedSpace Shat] {G F R : Drawing Shat}
  (hF : F.IsCircuitOf G)
    (hn : ¬ IsNullHomotopicOArc F.U) {a b : Shat} (ha : a ∈ F.V) (hb : b ∈ F.V) (hab : a ≠ b)
      (hR : R.IsPathOf G a b)
    (hV : R.V ∩ F.V ⊆ {a, b}) (hE : Disjoint R.E F.E) :
    ∃ P Q : Drawing Shat, P.IsPathBetween a b ∧ Q.IsPathBetween a b ∧ P.IsSubdrawing F
      ∧ Q.IsSubdrawing F ∧
      F.V = P.V ∪ Q.V ∧ F.E = P.E ∪ Q.E ∧ Disjoint P.E Q.E ∧ P.V ∩ Q.V = {a, b} ∧
        (G.sup P R).IsCircuit ∧
      ¬ IsNullHomotopicOArc (G.sup P R).U ∧ (G.sup P R).V = P.V ∪ R.V ∧ (G.sup P R).E = P.E ∪ R.E
        := by
  obtain ⟨hFG, hFc⟩ := hF
  obtain ⟨P, Q, hP, hQ, sP, sQ, -, -, hPQ, hdE, heq⟩ := hFc.exists_two_paths ha hb hab
  have hrs := hR.1
  have sPG := sP.trans hFG
  have sQG := sQ.trans hFG
  have hFV : F.V = P.V ∪ Q.V := by rw [← Drawing.sup_V sP sQ, heq]
  have hFE : F.E = P.E ∪ Q.E := by rw [← Drawing.sup_E sP sQ, heq]
  have hend : ∀ {D : Drawing Shat}, D.IsPathBetween a b → a ∈ D.V ∧ b ∈ D.V := fun {D} hD ↦ by
    obtain ⟨W, -, hV', -⟩ := hD
    rw [hV']
    exact ⟨W.start_mem_support, W.end_mem_support⟩
  have hint : ∀ {D : Drawing Shat}, D.V ⊆ F.V → D.IsPathBetween a b → R.V ∩ D.V = {a, b}
    := fun hsub hD ↦ by
    apply subset_antisymm
    · exact fun x hx ↦ hV ⟨hx.1, hsub hx.2⟩
    · rintro x (rfl | rfl)
      · exact ⟨(hend hR.2).1, (hend hD).1⟩
      · exact ⟨(hend hR.2).2, (hend hD).2⟩
  have hPF : P.V ⊆ F.V := hFV ▸ subset_union_left
  have hQF : Q.V ⊆ F.V := hFV ▸ subset_union_right
  have hdP : Disjoint R.E P.E := hE.mono_right (hFE ▸ subset_union_left)
  have hdQ : Disjoint R.E Q.E := hE.mono_right (hFE ▸ subset_union_right)
  have hcP : (G.sup P R).IsCircuit :=
    Drawing.isCircuit_sup hP hR.2 sPG hrs hab (by rw [inter_comm]; exact hint hPF hP) hdP.symm
  have hcQ : (G.sup Q R).IsCircuit :=
    Drawing.isCircuit_sup hQ hR.2 sQG hrs hab (by rw [inter_comm]; exact hint hQF hQ) hdQ.symm
  have hUP : (G.sup P R).U = R.U ∪ P.U := by
    rw [U_union (Drawing.sup_V sPG hrs) (Drawing.sup_E sPG hrs), union_comm]
  have hUQ : (G.sup Q R).U = Q.U ∪ R.U := U_union (Drawing.sup_V sQG hrs) (Drawing.sup_E sQG hrs)
  have hUF : F.U = P.U ∪ Q.U := U_union hFV hFE
  have hOP : IsOArc (G.sup P R).U := (IsCircuit.isOArc_U hcP)
  have hOQ : IsOArc (G.sup Q R).U := (IsCircuit.isOArc_U hcQ)
  by_cases h₁ : IsNullHomotopicOArc (G.sup P R).U
  · by_cases h₂ : IsNullHomotopicOArc (G.sup Q R).U
    · exfalso
      refine hn ?_
      rw [hUF]
      refine null_of_theta hT (isLine_of_isPathBetween hP hab) (isLine_of_isPathBetween hQ hab)
        (isLine_of_isPathBetween hR.2 hab) ?_ ?_ ?_ ?_ (hUQ ▸ hOQ) (hUP ▸ hOP) (hUQ ▸ h₂) (hUP ▸ h₁)
      · rw [U_inter_of_disjoint sPG sQG hdE, hPQ]
      · rw [U_inter_of_disjoint sQG hrs hdQ.symm, inter_comm]
        exact hint hQF hQ
      · rw [U_inter_of_disjoint hrs sPG hdP]
        exact hint hPF hP
      · rw [← hUF]
        exact IsCircuit.isOArc_U hFc
    · exact ⟨Q, P, hQ, hP, sQ, sP, by rw [hFV, union_comm], by rw [hFE, union_comm], hdE.symm,
        by rw [inter_comm, hPQ], hcQ, h₂, Drawing.sup_V sQG hrs,
        Drawing.sup_E sQG hrs⟩
  · exact ⟨P, Q, hP, hQ, sP, sQ, hFV, hFE, hdE, hPQ, hcP, h₁, Drawing.sup_V sPG hrs,
      Drawing.sup_E sPG hrs⟩

omit [T2Space Shat] in
theorem first_step {G Q : Drawing Shat} (hsub : Q.IsSubdrawing G) {a b : Shat} (hab : a ≠ b)
  (hQ : Q.IsPathBetween a b) :
    ∃ e ∈ Q.E, ∃ w ∈ Q.V, w ≠ a ∧ closure e ∩ G.V = {a, w} ∧ (w = b ∨ (w ≠ b ∧ 2 ≤ Q.E.ncard)) := by
  classical
  obtain ⟨W, hW, hV, hE⟩ := hQ
  cases W with
  | nil _ => exact absurd rfl hab
  | @cons _ w _ e h rest =>
    have hne : w ≠ a := by
      rintro rfl
      have : (Surface.GraphWalk.cons h rest).support = _ := rfl
      unfold Surface.GraphWalk.IsSimple at hW
      rw [this] at hW
      exact (List.nodup_cons.1 hW).1 rest.start_mem_support
    have hsetQ : closure e ∩ G.V = {a, w} := by
      rw [← hsub.closure_inter_V h.1]
      exact h.2.2.2
    refine ⟨e, h.1, w, h.2.2.1, hne, hsetQ, ?_⟩
    cases rest with
    | nil _ => exact Or.inl rfl
    | @cons _ w' _ e' h' rest' =>
      by_cases hwb : w = b
      · exact Or.inl hwb
      · right
        refine ⟨hwb, ?_⟩
        have hee : e ≠ e' := by
          rintro rfl
          have hs₁ : ({a, w} : Set Shat) = {w, w'} := h.2.2.2.symm.trans h'.2.2.2
          have ha' : a ∈ ({w, w'} : Set Shat) := hs₁ ▸ mem_insert _ _
          rcases ha' with rfl | ha'
          · exact hne rfl
          · obtain rfl : a = w' := ha'
            have hn : (a :: w :: a :: rest'.support).Nodup := by
              have : (a :: (w :: rest'.support)) = _ := rfl
              have h₂ : (Surface.GraphWalk.cons h (Surface.GraphWalk.cons h' rest')).support
                = a :: w :: rest'.support := rfl
              unfold Surface.GraphWalk.IsSimple at hW
              rw [h₂] at hW
              have h₃ : a ∈ rest'.support := rest'.start_mem_support
              exact absurd (List.mem_cons_of_mem _ h₃) (List.nodup_cons.1 hW).1
            exact absurd (by simp) (List.nodup_cons.1 hn).1
        have hsub₂ : ({e, e'} : Set (Set Shat)) ⊆ Q.E := by
          rw [hE]
          rintro x (rfl | rfl)
          · simp [Surface.GraphWalk.edges]
          · simp [Surface.GraphWalk.edges]
        have hfin : Q.E.Finite := Q.finite_edges
        calc 2 = ({e, e'} : Set (Set Shat)).ncard := (ncard_pair hee).symm
          _ ≤ Q.E.ncard := ncard_le_ncard hsub₂ hfin

variable (hS : IsSurface S)

omit [T2Space S] in
/-- The step that makes `F` smaller. `R` is a path outside `F` between two vertices of `F`, with its
inner vertices off
`Σ`. Each path of `F` between the two ends has an inner vertex in `Σ`, and it is at least as long as
`R`. -/
theorem exists_smaller_circuit (rad : RadialDrawing cap Γ) [ConnectedSpace Shat] {n : ℕ} {F R :
  Drawing Shat}
    (hF : IsShortCircuit rad n F) {a b : Shat} (ha : a ∈ F.V) (hb : b ∈ F.V) (hab : a ≠ b)
    (hR : R.IsPathOf rad.G a b) (hV : R.V ∩ F.V ⊆ {a, b}) (hE : Disjoint R.E F.E)
    (hVr : R.V ∩ range cap.emb ⊆ {a, b})
    (hQ : ∀ Q : Drawing Shat, Q.IsPathBetween a b → Q.IsSubdrawing F → R.E.ncard ≤ Q.E.ncard ∧
      ∃ w ∈ Q.V, w ≠ a ∧ w ≠ b ∧ w ∈ range cap.emb) :
    ∃ F', IsShortCircuit rad n F' ∧ (F'.V ∩ range cap.emb).ncard < (F.V ∩ range cap.emb).ncard := by
  obtain ⟨hFc, hnn, hlen⟩ := hF
  obtain ⟨P, Q, hP, hQp, sP, sQ, hFV, hFE, hdE, hPQ, hc, hnc, hcV, hcE⟩ :=
    exists_closing cap.isClosedSurface hFc hnn ha hb hab hR hV hE
  obtain ⟨hl, w, hwQ, hwa, hwb, hwr⟩ := hQ Q hQp sQ
  have hfG := rad.G
  have hEle : (rad.G.sup P R).E.ncard ≤ F.E.ncard := by
    rw [hcE, hFE, ncard_union_eq hdE P.finite_edges Q.finite_edges]
    exact (ncard_union_le _ _).trans (by omega)
  refine ⟨rad.G.sup P R, ⟨⟨rad.G.sup_isSubdrawing _ _, hc⟩, hnc, ?_⟩, ?_⟩
  · exact (Nat.div_le_div_right hEle).trans hlen
  · have hfin : (F.V ∩ range cap.emb).Finite := F.finite_V.inter_of_left _
    refine ncard_lt_ncard ⟨?_, ?_⟩ hfin
    · rintro x ⟨hx, hxr⟩
      rw [hcV] at hx
      rcases hx with hx | hx
      · exact ⟨hFV ▸ Or.inl hx, hxr⟩
      · rcases hVr ⟨hx, hxr⟩ with rfl | rfl
        · exact ⟨ha, hxr⟩
        · exact ⟨hb, hxr⟩
    · intro hsub
      have hwF : w ∈ F.V ∩ range cap.emb := ⟨hFV ▸ Or.inr hwQ, hwr⟩
      obtain ⟨h₁, -⟩ := hsub hwF
      rw [hcV] at h₁
      rcases h₁ with h₁ | h₁
      · have : w ∈ P.V ∩ Q.V := ⟨h₁, hwQ⟩
        rw [hPQ] at this
        rcases this with h | h
        · exact hwa h
        · exact hwb h
      · rcases hVr ⟨h₁, hwr⟩ with h | h
        · exact hwa h
        · exact hwb h

variable (rad : RadialDrawing cap Γ) (h3 : Γ.IsInternallyThreeConnected)
include hS

omit hS in
omit [T2Space S] [T2Space Shat] in
theorem RadialDrawing.other_end_Rstar {e : Set Shat} (he : e ∈ rad.G.E) {u : S} {w : Shat}
  (hu : u ∈ Γ.V)
    (hset : closure e ∩ rad.G.V = {cap.emb u, w}) : w ∈ rad.Rstar := by
  obtain ⟨v, hv, w', hw', h⟩ := rad.edge_ends he
  rw [hset] at h
  rcases (Set.pair_eq_pair_iff.1 h) with ⟨-, rfl⟩ | ⟨h₁, -⟩
  · exact hw'
  · exact absurd (⟨u, hu, rfl⟩ : cap.emb u ∈ Γ.hatV cap) (h₁ ▸ hw'.2)

omit [T2Space S] [T2Space Shat] in
omit hS in
/-- A neighbour in `Γ*` of a vertex on the cuff `Θ` is in `Σ`, unless it is the pole of `Θ`. -/
theorem RadialDrawing.step_in_range {e : Set Shat} (he : e ∈ rad.G.E) {u : S} {w p : Shat}
  (hu : u ∈ Γ.V) {Θ : Set S}
    (hΘ : Θ ∈ cuffs S) (huΘ : u ∈ Θ) (hp : p ∈ rad.poles) (hreg : rad.regionOf p = cap.cuffDisc Θ)
    (hset : closure e ∩ rad.G.V = {cap.emb u, w}) (hwp : w ≠ p) : w ∈ range cap.emb := by
  have hw := rad.other_end_Rstar he hu hset
  by_cases hpw : w ∈ rad.poles
  · exfalso
    obtain ⟨Θ', hΘ', hreg', -⟩ := rad.pole_cases hpw
    obtain ⟨-, huΘ'⟩ := rad.pole_edge he hpw hΘ' hreg' hset
    have hΘe : Θ' = Θ := by
      by_contra hne
      exact disjoint_left.1 (cuffs_disjoint hΘ' hΘ hne) huΘ' huΘ
    subst hΘe
    obtain ⟨-, -, hG3, -⟩ := id rad.isPreRadial
    exact hwp ((hG3 _ (rad.regionOf_mem hp.1).1).unique
      ⟨hreg.trans hreg'.symm ▸ (rad.regionOf_mem hpw.1).2, hpw.1.1⟩ ⟨(rad.regionOf_mem hp.1).2,
        hp.1.1⟩)
  · exact rad.region_subset_range hw hpw (rad.regionOf_mem hw).2

variable [ConnectedSpace Shat]
include h3

/-- Two vertices of `F` on the cuff of a pole outside `F` give a smaller circuit. -/
theorem exists_smaller_of_two {n : ℕ} {F : Drawing Shat} (hF : IsShortCircuit rad n F) {p : Shat}
  (hp : p ∈ rad.poles)
    (hpF : p ∉ F.V) {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hreg : rad.regionOf p
      = cap.cuffDisc Θ) {u v : S} (hu : u ∈ Γ.V)
    (hv : v ∈ Γ.V) (huΘ : u ∈ Θ) (hvΘ : v ∈ Θ) (hne : u ≠ v) (hu' : cap.emb u ∈ F.V)
      (hv' : cap.emb v ∈ F.V) :
    ∃ F', IsShortCircuit rad n F' ∧ (F'.V ∩ range cap.emb).ncard < (F.V ∩ range cap.emb).ncard := by
  classical
  have hpm : p ∉ range cap.emb := cap.notMem_range hΘ (hreg ▸ (rad.regionOf_mem hp.1).2)
  obtain ⟨e₁, he₁, hs₁⟩ := rad.exists_pole_edge hS h3 hp hΘ hreg hu huΘ
  obtain ⟨e₂, he₂, hs₂⟩ := rad.exists_pole_edge hS h3 hp hΘ hreg hv hvΘ
  have hG : ∀ {w : S}, w ∈ Γ.V → cap.emb w ∈ rad.G.V := fun hw ↦ rad.isPreRadial.2.1 ⟨_, hw, rfl⟩
  have hpG : p ∈ rad.G.V := hp.1.1
  have hl₁ : rad.G.toGraph.IsLink e₁ (cap.emb u) p := ⟨he₁, hG hu, hpG, hs₁⟩
  have hl₂ : rad.G.toGraph.IsLink e₂ p (cap.emb v) :=
    ⟨he₂, hpG, hG hv, by rw [Set.pair_comm]; exact hs₂⟩
  let M : Surface.GraphWalk rad.G.toGraph (cap.emb u) (cap.emb v) := .cons hl₁ (.cons hl₂ (.nil
    (hG hv)))
  have hsupp : M.support = [cap.emb u, p, cap.emb v] := rfl
  have hedge : M.edges = [e₁, e₂] := rfl
  have hemb : cap.emb u ≠ cap.emb v := fun h ↦ hne (cap.isEmbedding.injective h)
  have hu₁ : cap.emb u ≠ p := fun h ↦ hpm ⟨u, h⟩
  have hv₁ : p ≠ cap.emb v := fun h ↦ hpm ⟨v, h.symm⟩
  have hsimple : M.IsSimple := by
    unfold Surface.GraphWalk.IsSimple
    rw [hsupp]
    simp [hu₁, hemb, hv₁]
  set R := walkDrawing rad.G M with hRdef
  have hRV : ∀ z, z ∈ R.V ↔ z = cap.emb u ∨ z = p ∨ z = cap.emb v := fun z ↦ by
    rw [hRdef, walkDrawing_V, mem_ofPred_eq, hsupp]
    simp
  have hRE : R.E ⊆ {e₁, e₂} := fun z hz ↦ by
    rw [hRdef, walkDrawing_E, mem_ofPred_eq, hedge] at hz
    simpa using hz
  have hsubF := hF.1.1
  have hE₁ : ∀ {e} {x}, closure e ∩ rad.G.V = {x, p} → e ∉ F.E := fun {e x} hs he ↦ by
    have : p ∈ closure e ∩ F.V := by
      rw [hsubF.closure_inter_V he, hs]
      exact mem_insert_of_mem _ rfl
    exact hpF this.2
  refine exists_smaller_circuit rad hF hu' hv' hemb ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hsimple⟩ ?_ ?_ ?_
    fun Q hQ hsQ ↦ ?_
  · rintro z ⟨hz, hzF⟩
    rcases (hRV z).1 hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hzF hpF
    · exact Or.inr rfl
  · refine disjoint_left.2 fun e he heF ↦ ?_
    rcases hRE he with rfl | rfl
    · exact hE₁ hs₁ heF
    · exact hE₁ hs₂ heF
  · rintro z ⟨hz, hzr⟩
    rcases (hRV z).1 hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hzr hpm
    · exact Or.inr rfl
  · obtain ⟨e, he, w, hw, hwa, hset, hend⟩ := first_step (hsQ.trans hsubF) hemb hQ
    have heG := hsubF.2 (hsQ.2 he)
    have hwR := rad.other_end_Rstar heG hu hset
    have hwp : w ≠ p := fun h ↦ hpF (hsQ.1 (h ▸ hw))
    have hwb : w ≠ cap.emb v := fun h ↦ hwR.2 ⟨v, hv, h.symm⟩
    refine ⟨?_, w, hw, hwa, hwb, rad.step_in_range heG hu hΘ huΘ hp hreg hset hwp⟩
    have h₂ : 2 ≤ Q.E.ncard := (hend.resolve_left hwb).2
    exact (ncard_le_ncard hRE (toFinite _)).trans ((ncard_insert_le _ _).trans (by simpa using h₂))

/-- A vertex of `F` on the cuff of a pole of `F` that is not next to the pole in `F` gives a smaller
circuit. -/
theorem exists_smaller_of_pole {n : ℕ} {F : Drawing Shat} (hF : IsShortCircuit rad n F) {p : Shat}
  (hp : p ∈ rad.poles)
    (hpF : p ∈ F.V) {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hreg : rad.regionOf p = cap.cuffDisc Θ) {v : S}
    (hv : v ∈ Γ.V) (hvΘ : v ∈ Θ) (hv' : cap.emb v ∈ F.V)
    (hno : ∀ e ∈ F.E, closure e ∩ rad.G.V ≠ {cap.emb v, p}) :
    ∃ F', IsShortCircuit rad n F' ∧ (F'.V ∩ range cap.emb).ncard < (F.V ∩ range cap.emb).ncard := by
  classical
  have hpm : p ∉ range cap.emb := cap.notMem_range hΘ (hreg ▸ (rad.regionOf_mem hp.1).2)
  obtain ⟨e₁, he₁, hs₁⟩ := rad.exists_pole_edge hS h3 hp hΘ hreg hv hvΘ
  have hG : cap.emb v ∈ rad.G.V := rad.isPreRadial.2.1 ⟨_, hv, rfl⟩
  have hpG : p ∈ rad.G.V := hp.1.1
  have hl₁ : rad.G.toGraph.IsLink e₁ p (cap.emb v) :=
    ⟨he₁, hpG, hG, by rw [Set.pair_comm]; exact hs₁⟩
  let M : Surface.GraphWalk rad.G.toGraph p (cap.emb v) := .cons hl₁ (.nil hG)
  have hsupp : M.support = [p, cap.emb v] := rfl
  have hedge : M.edges = [e₁] := rfl
  have hne : p ≠ cap.emb v := fun h ↦ hpm ⟨v, h.symm⟩
  have hsimple : M.IsSimple := by
    unfold Surface.GraphWalk.IsSimple
    rw [hsupp]
    simp [hne]
  set R := walkDrawing rad.G M with hRdef
  have hRV : ∀ z, z ∈ R.V ↔ z = p ∨ z = cap.emb v := fun z ↦ by
    rw [hRdef, walkDrawing_V, mem_ofPred_eq, hsupp]
    simp
  have hRE : R.E ⊆ {e₁} := fun z hz ↦ by
    rw [hRdef, walkDrawing_E, mem_ofPred_eq, hedge] at hz
    simpa using hz
  have hsubF := hF.1.1
  refine exists_smaller_circuit rad hF hpF hv' hne ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hsimple⟩ ?_ ?_ ?_
    fun Q hQ hsQ ↦ ?_
  · rintro z ⟨hz, -⟩
    exact (hRV z).1 hz
  · refine disjoint_left.2 fun e he heF ↦ ?_
    rcases hRE he with rfl
    exact hno e heF hs₁
  · rintro z ⟨hz, -⟩
    exact (hRV z).1 hz
  · obtain ⟨e, he, w, hw, hwa, hset, hend⟩ := first_step (hsQ.trans hsubF) hne hQ
    have heG := hsubF.2 (hsQ.2 he)
    obtain ⟨u, hu, w', hw', hset'⟩ := rad.edge_ends heG
    have hset₂ : ({p, w} : Set Shat) = {cap.emb u, w'} := hset.symm.trans hset'
    have hwu : w = cap.emb u := by
      rcases Set.pair_eq_pair_iff.1 hset₂ with ⟨h₁, -⟩ | ⟨-, h₁⟩
      · exact absurd ⟨u, h₁.symm⟩ hpm
      · exact h₁
    have hwb : w ≠ cap.emb v := by
      intro h
      refine hno e (hsQ.2 he) ?_
      rw [hset, h, Set.pair_comm]
    refine ⟨?_, w, hw, hwa, hwb, ⟨u, hwu.symm⟩⟩
    have h₂ : 2 ≤ Q.E.ncard := (hend.resolve_left hwb).2
    have h₃ := ncard_le_ncard hRE (toFinite _)
    rw [ncard_singleton] at h₃
    exact h₃.trans (by omega)

end GraphMinor.GM19
