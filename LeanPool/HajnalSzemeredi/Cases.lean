/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.HajnalSzemeredi.Shift
public import LeanPool.HajnalSzemeredi.Structure

/-!
Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.

# Los dos casos de recoloreo del Teorema 2.4 de Kierstead–Kostochka

Contexto: `Ctx G S P c r s lo hi` (clase grande inaccesible), `U` y `𝒜' = T_U` como en
`Ctx.exists_TU`, un vértice solo `z` con color `W = c z ∈ 𝒜'`, un vecino especial
`y₁ ∈ S_z ⊆ B`, y una coloración equitativa `g` de `B⁻ = B \ {y₁}` con la paleta `ℬ = P \ 𝒜`
(dada por la hipótesis de inducción primaria).

* **Caso 1** (`case1`): `z` es movible a una clase `X ∈ 𝒜 \ {W}`. Se mueve `z` a `X` y `y₁` a
  `W`; la coloración de `A⁺ = A ∪ {y₁}` es equitativa o casi equitativa con clase grande
  `X ∪ {z}` accesible (porque `W` es terminal), y por el Lema 2.1 se vuelve equitativa; junto con
  `g` da una coloración equitativa de `S`.
* **Caso 2** (`case2`): `z` no es movible a ninguna clase de `𝒜` y tiene dos vecinos especiales
  `y₁ ≠ y₂` no adyacentes. Se mueve `y₁` a `W` y `z` a una clase `Y` de `g` sin vecinos de `z`;
  se obtiene una coloración casi equitativa con estrictamente más clases accesibles.
-/

@[expose] public section

noncomputable section

open Finset Relation

namespace HajnalSzemeredi

variable {V : Type*} {G : SimpleGraph V}

open Classical in
private lemma proper_mono' {S T : Finset V} {f : V → ℕ} (h : Proper G S f) (hT : T ⊆ S) :
    Proper G T f :=
  fun v hv w hw => h v (hT hv) w (hT hw)

open Classical in
private lemma proper_insert_update {T : Finset V} {f : V → ℕ} {v : V} {j : ℕ}
    (h : Proper G T f) (hmov : Movable G T f v j) :
    Proper G (insert v T) (Function.update f v j) := by
  intro a ha b hb hab
  by_cases hav : a = v
  · subst hav
    have hba : b ≠ a := fun h => G.loopless.irrefl _ (h ▸ hab)
    have hbT : b ∈ T := (mem_insert.mp hb).resolve_left hba
    simp only [Function.update_self, Function.update_of_ne hba]
    intro hjb
    exact hmov b (mem_cls.mpr ⟨hbT, hjb.symm⟩) hab
  · have haT : a ∈ T := (mem_insert.mp ha).resolve_left hav
    by_cases hbv : b = v
    · subst hbv
      simp only [Function.update_self, Function.update_of_ne hav]
      intro hja
      exact hmov a (mem_cls.mpr ⟨haT, hja⟩) hab.symm
    · have hbT : b ∈ T := (mem_insert.mp hb).resolve_left hbv
      simpa [Function.update_of_ne hav, Function.update_of_ne hbv] using h a haT b hbT hab

open Classical in
private lemma cls_insert_update_self {T : Finset V} {f : V → ℕ} {v : V} {j : ℕ} :
    cls (insert v T) (Function.update f v j) j = insert v (cls T f j) := by
  ext w
  by_cases hw : w = v
  · subst hw; simp
  · simp [hw]

open Classical in
private lemma cls_insert_update_ne {T : Finset V} {f : V → ℕ} {v : V} {i j : ℕ}
    (hv : v ∉ T) (hij : i ≠ j) :
    cls (insert v T) (Function.update f v j) i = cls T f i := by
  ext w
  by_cases hw : w = v
  · subst hw; simp [hv, Ne.symm hij]
  · simp [hw]

open Classical in
private lemma cls_erase' {T : Finset V} {f : V → ℕ} {v : V} {i : ℕ} :
    cls (T.erase v) f i = (cls T f i).erase v := by
  ext w
  simp [and_assoc]

open Classical in
private lemma cls_part {S : Finset V} {c : V → ℕ} {Q : Finset ℕ} {i : ℕ} (hi : i ∈ Q) :
    cls (part S c Q) c i = cls S c i := by
  ext w
  simp only [mem_cls, part, mem_filter]
  constructor
  · rintro ⟨⟨hw, -⟩, hc⟩; exact ⟨hw, hc⟩
  · rintro ⟨hw, hc⟩; exact ⟨⟨hw, hc ▸ hi⟩, hc⟩

open Classical in
private lemma solo_eq {S : Finset V} {c : V → ℕ} {y z u : V} {W : ℕ}
    (h : nIn G S c y W = {z}) (hu : u ∈ S) (hcu : c u = W) (hadj : G.Adj y u) : u = z := by
  have : u ∈ nIn G S c y W := mem_inter.mpr ⟨mem_nbr.mpr ⟨hu, hadj⟩, mem_cls.mpr ⟨hu, hcu⟩⟩
  rw [h] at this
  exact mem_singleton.mp this

open Classical in
private lemma proper_comb {S SA SB : Finset V} {PA PB : Finset ℕ} {cA cB : V → ℕ}
    (hA : Proper G SA cA) (hB : Proper G SB cB) (hiA : Into SA cA PA) (hiB : Into SB cB PB)
    (hS : SA ∪ SB = S) (hPdisj : Disjoint PA PB) :
    Proper G S (fun v => if v ∈ SA then cA v else cB v) := by
  intro v hv w hw hvw
  have hv' : v ∈ SA ∪ SB := hS ▸ hv
  have hw' : w ∈ SA ∪ SB := hS ▸ hw
  by_cases hvA : v ∈ SA <;> by_cases hwA : w ∈ SA <;> simp only [hvA, hwA, ite_true, ite_false]
  · exact hA v hvA w hwA hvw
  · have hwB : w ∈ SB := (mem_union.mp hw').resolve_left hwA
    intro heq
    exact disjoint_left.mp hPdisj (hiA v hvA) (heq ▸ hiB w hwB)
  · have hvB : v ∈ SB := (mem_union.mp hv').resolve_left hvA
    intro heq
    exact disjoint_left.mp hPdisj (hiA w hwA) (heq ▸ hiB v hvB)
  · exact hB v ((mem_union.mp hv').resolve_left hvA) w ((mem_union.mp hw').resolve_left hwA) hvw

open Classical in
private lemma into_comb {S SA SB : Finset V} {P PA PB : Finset ℕ} {cA cB : V → ℕ}
    (hiA : Into SA cA PA) (hiB : Into SB cB PB) (hS : SA ∪ SB = S) (hP : PA ∪ PB = P) :
    Into S (fun v => if v ∈ SA then cA v else cB v) P := by
  intro v hv
  have hv' : v ∈ SA ∪ SB := hS ▸ hv
  rw [← hP]
  by_cases hvA : v ∈ SA
  · simp only [hvA, ite_true]; exact mem_union_left _ (hiA v hvA)
  · simp only [hvA, ite_false]
    exact mem_union_right _ (hiB v ((mem_union.mp hv').resolve_left hvA))

open Classical in
private lemma cls_comb_A {S SA SB : Finset V} {PA PB : Finset ℕ} {cA cB : V → ℕ} {i : ℕ}
    (hiB : Into SB cB PB) (hS : SA ∪ SB = S) (hPdisj : Disjoint PA PB) (hi : i ∈ PA) :
    cls S (fun v => if v ∈ SA then cA v else cB v) i = cls SA cA i := by
  ext v
  simp only [mem_cls]
  constructor
  · rintro ⟨hv, hc⟩
    by_cases hvA : v ∈ SA
    · simp only [hvA, ite_true] at hc; exact ⟨hvA, hc⟩
    · simp only [hvA, ite_false] at hc
      have hvB : v ∈ SB := (mem_union.mp (hS ▸ hv : v ∈ SA ∪ SB)).resolve_left hvA
      exact absurd (hc ▸ hiB v hvB) (disjoint_left.mp hPdisj hi)
  · rintro ⟨hv, hc⟩
    exact ⟨hS ▸ mem_union_left _ hv, by simp only [hv, ite_true]; exact hc⟩

open Classical in
private lemma cls_comb_B {S SA SB : Finset V} {PA PB : Finset ℕ} {cA cB : V → ℕ} {i : ℕ}
    (hiA : Into SA cA PA) (hS : SA ∪ SB = S) (hdisj : Disjoint SA SB)
    (hPdisj : Disjoint PA PB) (hi : i ∈ PB) :
    cls S (fun v => if v ∈ SA then cA v else cB v) i = cls SB cB i := by
  ext v
  simp only [mem_cls]
  constructor
  · rintro ⟨hv, hc⟩
    by_cases hvA : v ∈ SA
    · simp only [hvA, ite_true] at hc
      exact absurd hi (disjoint_left.mp hPdisj (hc ▸ hiA v hvA))
    · simp only [hvA, ite_false] at hc
      exact ⟨(mem_union.mp (hS ▸ hv : v ∈ SA ∪ SB)).resolve_left hvA, hc⟩
  · rintro ⟨hv, hc⟩
    have hvA : v ∉ SA := fun h => disjoint_left.mp hdisj h hv
    exact ⟨hS ▸ mem_union_right _ hv, by simp only [hvA, ite_false]; exact hc⟩

open Classical in
private lemma reach_restrict {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ}
    (h : Ctx G S P c r s lo hi) {R : ℕ → ℕ → Prop}
    (hR : ∀ a b, R a b → Mov G S c a b) {X : ℕ} (hX : ReflTransGen R X lo) :
    ReflTransGen (fun a b => R a b ∧ a ∈ acc G S P c lo ∧ b ∈ acc G S P c lo) X lo := by
  have key : ∀ a, ReflTransGen R a lo → a ∈ acc G S P c lo ∧
      ReflTransGen (fun a b => R a b ∧ a ∈ acc G S P c lo ∧ b ∈ acc G S P c lo) a lo := by
    intro a ha
    induction ha using ReflTransGen.head_induction_on with
    | refl => exact ⟨h.lo_mem_acc, ReflTransGen.refl⟩
    | head hab _ ih =>
      have hm := h.mem_acc_of_mov (hR _ _ hab) ih.1
      exact ⟨hm, ReflTransGen.head ⟨hab, hm, ih.1⟩ ih.2⟩
  exact (key X hX).2

open Classical in
/-- Pegado de dos coloraciones equitativas de partes disjuntas con paletas disjuntas. -/
theorem isEq_combine {S SA SB : Finset V} {P PA PB : Finset ℕ} {cA cB : V → ℕ} {s : ℕ}
    (hA : IsEq G SA PA cA s) (hB : IsEq G SB PB cB s) (hS : SA ∪ SB = S)
    (hdisj : Disjoint SA SB) (hP : PA ∪ PB = P) (hPdisj : Disjoint PA PB) :
    IsEq G S P (fun v => if v ∈ SA then cA v else cB v) s := by
  refine ⟨proper_comb hA.proper hB.proper hA.into hB.into hS hPdisj,
    into_comb hA.into hB.into hS hP, fun i hi => ?_⟩
  rcases mem_union.mp (hP ▸ hi : i ∈ PA ∪ PB) with hi' | hi'
  · rw [cls_comb_A hB.into hS hPdisj hi']; exact hA.card i hi'
  · rw [cls_comb_B hA.into hS hdisj hPdisj hi']; exact hB.card i hi'

open Classical in
theorem case1 {S : Finset V} {P : Finset ℕ} {c g : V → ℕ} {r s lo hi U : ℕ} {z y₁ : V}
    (h : Ctx G S P c r s lo hi)
    (hterm : ∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
      ReflTransGen (avoid G S c W) X lo)
    (hzS : z ∈ S) (hzT : c z ∈ T G S P c lo U)
    (hy₁ : y₁ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hX : ∃ X ∈ acc G S P c lo, X ≠ c z ∧ Movable G S c z X)
    (hg : IsEq G ((part S c (P \ acc G S P c lo)).erase y₁) (P \ acc G S P c lo) g s) :
    ∃ c', IsEq G S P c' s := by
  obtain ⟨X, hXacc, hXW, hXmov⟩ := hX
  set PA := acc G S P c lo with hPA
  set PB := P \ PA with hPB
  set A := part S c PA with hA
  set B := part S c PB with hB
  have hWacc : c z ∈ PA := (mem_erase.mp (Ctx.T_subset U hzT)).2
  have hWlo : c z ≠ lo := by
    intro e
    have hz' := hzT
    rw [e] at hz'
    exact Ctx.lo_notMem_T U hz'
  have hWhi : c z ≠ hi := fun e => h.hi_not (e ▸ hWacc)
  have hWcard : (cls S c (c z)).card = s := h.near.card _ (Ctx.acc_subset hWacc) hWlo hWhi
  obtain ⟨hy₁B, hsolo⟩ := mem_filter.mp hy₁
  obtain ⟨-, -, -, hsolo₁⟩ := hsolo
  have hy₁S : y₁ ∈ S := (mem_filter.mp hy₁B).1
  have hy₁PB : c y₁ ∈ PB := (mem_filter.mp hy₁B).2
  have hy₁PA : c y₁ ∉ PA := (mem_sdiff.mp hy₁PB).2
  have hzA : z ∈ A := mem_filter.mpr ⟨hzS, hWacc⟩
  have hy₁A : y₁ ∉ A := fun hh => hy₁PA (mem_filter.mp hh).2
  have hXlo_hi : X ≠ hi := fun e => h.hi_not (e ▸ hXacc)
  set c1 := Function.update c z X with hc1
  set φ := Function.update c1 y₁ (c z) with hφ
  set SA := insert y₁ A with hSA
  have hc1prop : Proper G A c1 :=
    proper_mono' (proper_update h.near.proper hXmov) (filter_subset _ _)
  have hmov1 : Movable G A c1 y₁ (c z) := by
    intro w hw hadj
    rw [mem_cls] at hw
    have hwz : w ≠ z := by
      rintro rfl
      rw [hc1, Function.update_self] at hw
      exact hXW hw.2
    rw [hc1, Function.update_of_ne hwz] at hw
    exact hwz (solo_eq hsolo₁ (mem_filter.mp hw.1).1 hw.2 hadj)
  have hprop : Proper G SA φ := proper_insert_update hc1prop hmov1
  have hinto : Into SA φ PA := by
    intro v hv
    by_cases hvy : v = y₁
    · subst hvy; simpa [hφ] using hWacc
    · have hvA : v ∈ A := (mem_insert.mp hv).resolve_left hvy
      rw [hφ, Function.update_of_ne hvy]
      by_cases hvz : v = z
      · subst hvz; simpa [hc1] using hXacc
      · rw [hc1, Function.update_of_ne hvz]; exact (mem_filter.mp hvA).2
  have hclsW : cls SA φ (c z) = insert y₁ ((cls S c (c z)).erase z) := by
    rw [hSA, hφ, cls_insert_update_self, hc1, cls_update_old hXW.symm, cls_part hWacc]
  have hclsWcard : (cls SA φ (c z)).card = s := by
    rw [hclsW, card_insert_of_notMem, card_erase_of_mem (mem_cls.mpr ⟨hzS, rfl⟩), hWcard]
    · have : 0 < s := hWcard ▸ card_pos.mpr ⟨z, mem_cls.mpr ⟨hzS, rfl⟩⟩
      omega
    · intro hm
      exact hy₁PA ((mem_cls.mp (mem_erase.mp hm).2).2 ▸ hWacc)
  have hclsX : cls SA φ X = insert z (cls S c X) := by
    rw [hSA, hφ, cls_insert_update_ne hy₁A hXW, hc1, cls_update_self hzA, cls_part hXacc]
  have hclsXcard : (cls SA φ X).card = (cls S c X).card + 1 := by
    rw [hclsX, card_insert_of_notMem]
    intro hm
    exact hXW (mem_cls.mp hm).2.symm
  have hclsO : ∀ i ∈ PA, i ≠ c z → i ≠ X → cls SA φ i = cls S c i := by
    intro i hi hiW hiX
    rw [hSA, hφ, cls_insert_update_ne hy₁A hiW, hc1, cls_update_other hiX hiW, cls_part hi]
  have hEqA : ∃ cA, IsEq G SA PA cA s := by
    by_cases hXlo : X = lo
    · refine ⟨φ, hprop, hinto, fun i hi' => ?_⟩
      by_cases hiW : i = c z
      · rw [hiW]; exact hclsWcard
      by_cases hiX : i = X
      · rw [hiX, hclsXcard, hXlo]; exact h.near.card_lo
      rw [hclsO i hi' hiW hiX]
      exact h.near.card i (Ctx.acc_subset hi') (hXlo ▸ hiX) (fun e => h.hi_not (e ▸ hi'))
    · have hXcard : (cls S c X).card = s := h.near.card X (Ctx.acc_subset hXacc) hXlo hXlo_hi
      have hnear : IsNear G SA PA φ s lo X := by
        refine ⟨hprop, hinto, h.lo_mem_acc, hXacc, Ne.symm hXlo, ?_, ?_, ?_⟩
        · rw [hclsO lo h.lo_mem_acc (Ne.symm hWlo) (Ne.symm hXlo)]; exact h.near.card_lo
        · rw [hclsXcard, hXcard]
        · intro i hi' hilo hiX
          by_cases hiW : i = c z
          · rw [hiW]; exact hclsWcard
          rw [hclsO i hi' hiW hiX]
          exact h.near.card i (Ctx.acc_subset hi') hilo (fun e => h.hi_not (e ▸ hi'))
      refine shift_of_acc hnear ?_
      have hp := reach_restrict h (fun a b hab => hab.1)
        (hterm (c z) hzT X (mem_erase.mpr ⟨hXW, hXacc⟩))
      refine transfer hp fun a b hab hbX => ?_
      obtain ⟨⟨⟨v, hv, hvmov⟩, haW, hbW⟩, haA, hbA⟩ := hab
      rw [mem_cls] at hv
      have hvz : v ≠ z := by rintro rfl; exact haW hv.2.symm
      have hvy : v ≠ y₁ := by rintro rfl; exact hy₁PA (hv.2 ▸ haA)
      refine ⟨v, mem_cls.mpr ⟨mem_insert_of_mem (mem_filter.mpr ⟨hv.1, hv.2 ▸ haA⟩), ?_⟩, ?_⟩
      · rw [hφ, Function.update_of_ne hvy, hc1, Function.update_of_ne hvz]; exact hv.2
      · intro u hu
        rw [hclsO b hbA hbW hbX] at hu
        exact hvmov u hu
  obtain ⟨cA, hcA⟩ := hEqA
  refine ⟨_, isEq_combine hcA hg ?_ ?_ (union_sdiff_of_subset Ctx.acc_subset) disjoint_sdiff⟩
  · ext v
    constructor
    · intro hv
      rcases mem_union.mp hv with hv | hv
      · rcases mem_insert.mp hv with rfl | hv
        · exact hy₁S
        · exact (mem_filter.mp hv).1
      · exact (mem_filter.mp (mem_erase.mp hv).2).1
    · intro hv
      by_cases hvy : v = y₁
      · subst hvy; exact mem_union_left _ (mem_insert_self _ _)
      by_cases hvA : c v ∈ PA
      · exact mem_union_left _ (mem_insert_of_mem (mem_filter.mpr ⟨hv, hvA⟩))
      · exact mem_union_right _
          (mem_erase.mpr ⟨hvy, mem_filter.mpr ⟨hv, mem_sdiff.mpr ⟨h.near.into v hv, hvA⟩⟩⟩)
  · rw [disjoint_left]
    intro v hv1 hv2
    obtain ⟨hvy, hvB⟩ := mem_erase.mp hv2
    rcases mem_insert.mp hv1 with rfl | hvA
    · exact hvy rfl
    · exact (mem_sdiff.mp (mem_filter.mp hvB).2).2 (mem_filter.mp hvA).2

open Classical in
/-- A blocked vertex has a free class after one neighbor is removed. -/
private lemma exists_free_class {S : Finset V} {P : Finset ℕ} {c : V → ℕ}
    {r s lo hi : ℕ} {z y₁ : V} (h : Ctx G S P c r s lo hi)
    (hzS : z ∈ S) (hWacc : c z ∈ acc G S P c lo) (hy₁S : y₁ ∈ S)
    (hy₁PA : c y₁ ∉ acc G S P c lo) (hadjzy : G.Adj z y₁)
    (hnot : ∀ X ∈ acc G S P c lo, X ≠ c z → ¬ Movable G S c z X) (g : V → ℕ) :
    ∃ Y ∈ P \ acc G S P c lo,
      Movable G ((part S c (P \ acc G S P c lo)).erase y₁) g z Y := by
  set PA := acc G S P c lo
  set PB := P \ PA
  set A := part S c PA
  set B := part S c PB
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hN1 : (PA.erase (c z)).card ≤ (nbr G A z).card := by
    refine le_trans (card_le_card ?_) (card_image_le (f := c))
    intro X hX
    obtain ⟨hXW, hXA⟩ := mem_erase.mp hX
    have := hnot X hXA hXW
    simp only [Movable, not_forall, not_not] at this
    obtain ⟨w, hw, hadj⟩ := this
    rw [mem_cls] at hw
    exact mem_image.mpr ⟨w, mem_nbr.mpr ⟨mem_filter.mpr ⟨hw.1, hw.2 ▸ hXA⟩, hadj⟩, hw.2⟩
  have hN2 : PB.card ≤ (nbr G (B.erase y₁) z).card := by
    refine le_trans (card_le_card ?_) (card_image_le (f := g))
    intro Y hY
    have := hcon Y hY
    simp only [Movable, not_forall, not_not] at this
    obtain ⟨w, hw, hadj⟩ := this
    rw [mem_cls] at hw
    exact mem_image.mpr ⟨w, mem_nbr.mpr ⟨hw.1, hadj⟩, hw.2⟩
  have hsub : nbr G A z ∪ insert y₁ (nbr G (B.erase y₁) z) ⊆ nbr G S z := by
    intro w hw
    rcases mem_union.mp hw with hw | hw
    · obtain ⟨hwA, hadj⟩ := mem_nbr.mp hw
      exact mem_nbr.mpr ⟨(mem_filter.mp hwA).1, hadj⟩
    · rcases mem_insert.mp hw with rfl | hw
      · exact mem_nbr.mpr ⟨hy₁S, hadjzy⟩
      · obtain ⟨hwB, hadj⟩ := mem_nbr.mp hw
        exact mem_nbr.mpr ⟨(mem_filter.mp (mem_erase.mp hwB).2).1, hadj⟩
  have hdis : Disjoint (nbr G A z) (insert y₁ (nbr G (B.erase y₁) z)) := by
    rw [disjoint_left]
    intro w hw1 hw2
    have hwA := (mem_filter.mp (mem_nbr.mp hw1).1).2
    rcases mem_insert.mp hw2 with rfl | hw2
    · exact hy₁PA hwA
    · exact (mem_sdiff.mp (mem_filter.mp (mem_erase.mp (mem_nbr.mp hw2).1).2).2).2 hwA
  have hy₁n : y₁ ∉ nbr G (B.erase y₁) z := by simp
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis, card_insert_of_notMem hy₁n] at hc
  have hdeg := h.deg z hzS
  have hr := h.card_r
  have he := card_erase_add_one hWacc
  have hk1 : PA.card = (acc G S P c lo).card := rfl
  have hk2 : PB.card = (P \ acc G S P c lo).card := rfl
  omega

open Classical in
theorem case2 {S : Finset V} {P : Finset ℕ} {c g : V → ℕ} {r s lo hi U : ℕ} {z y₁ y₂ : V}
    (h : Ctx G S P c r s lo hi)
    (hterm : ∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
      ReflTransGen (avoid G S c W) X lo)
    (hzS : z ∈ S) (hzT : c z ∈ T G S P c lo U)
    (hnot : ∀ X ∈ acc G S P c lo, X ≠ c z → ¬ Movable G S c z X)
    (hy₁ : y₁ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hy₂ : y₂ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hne : y₁ ≠ y₂) (hnadj : ¬ G.Adj y₁ y₂)
    (hg : IsEq G ((part S c (P \ acc G S P c lo)).erase y₁) (P \ acc G S P c lo) g s) :
    ∃ c' hi', IsNear G S P c' s lo hi' ∧
      (acc G S P c lo).card < (acc G S P c' lo).card := by
  set PA := acc G S P c lo with hPA
  set PB := P \ PA with hPB
  set A := part S c PA with hA
  set B := part S c PB with hB
  have hWacc : c z ∈ PA := (mem_erase.mp (Ctx.T_subset U hzT)).2
  have hWlo : c z ≠ lo := by
    intro e
    have hz' := hzT
    rw [e] at hz'
    exact Ctx.lo_notMem_T U hz'
  have hWhi : c z ≠ hi := fun e => h.hi_not (e ▸ hWacc)
  have hWcard : (cls S c (c z)).card = s := h.near.card _ (Ctx.acc_subset hWacc) hWlo hWhi
  obtain ⟨hy₁B, hsolo⟩ := mem_filter.mp hy₁
  obtain ⟨-, -, -, hsolo₁⟩ := hsolo
  obtain ⟨hy₂B, hsolo'⟩ := mem_filter.mp hy₂
  obtain ⟨-, -, -, hsolo₂⟩ := hsolo'
  have hy₁S : y₁ ∈ S := (mem_filter.mp hy₁B).1
  have hy₁PB : c y₁ ∈ PB := (mem_filter.mp hy₁B).2
  have hy₁PA : c y₁ ∉ PA := (mem_sdiff.mp hy₁PB).2
  have hzA : z ∈ A := mem_filter.mpr ⟨hzS, hWacc⟩
  have hzB : z ∉ B := fun hh => (mem_sdiff.mp (mem_filter.mp hh).2).2 hWacc
  have hy₁A : y₁ ∉ A := fun hh => hy₁PA (mem_filter.mp hh).2
  have hzy : z ≠ y₁ := by rintro rfl; exact hy₁A hzA
  have hadjzy : G.Adj z y₁ := by
    have : z ∈ nIn G S c y₁ (c z) := by rw [hsolo₁]; exact mem_singleton_self _
    exact (mem_nbr.mp (mem_inter.mp this).1).2.symm
  have hPdisj : Disjoint PA PB := disjoint_sdiff
  have hPU : PA ∪ PB = P := union_sdiff_of_subset Ctx.acc_subset
  have hYex := exists_free_class h hzS hWacc hy₁S hy₁PA hadjzy hnot g
  obtain ⟨Y, hYPB, hYmov⟩ := hYex
  change Y ∈ PB at hYPB
  have hYPA : Y ∉ PA := (mem_sdiff.mp hYPB).2
  -- the new colouring
  set SA := insert y₁ (A.erase z) with hSA
  set φ := Function.update c y₁ (c z) with hφ
  set SB := insert z (B.erase y₁) with hSB
  set g' := Function.update g z Y with hg'
  have hy₁SA : y₁ ∉ A.erase z := fun hh => hy₁A (mem_erase.mp hh).2
  have hzSB : z ∉ B.erase y₁ := fun hh => hzB (mem_erase.mp hh).2
  have hpropA : Proper G SA φ := by
    refine proper_insert_update (proper_mono' h.near.proper
      (fun v hv => (mem_filter.mp (mem_erase.mp hv).2).1)) ?_
    intro w hw hadj
    rw [mem_cls] at hw
    obtain ⟨hwz, hwA⟩ := mem_erase.mp hw.1
    exact hwz (solo_eq hsolo₁ (mem_filter.mp hwA).1 hw.2 hadj)
  have hintoA : Into SA φ PA := by
    intro v hv
    by_cases hvy : v = y₁
    · subst hvy; simpa [hφ] using hWacc
    · have hvA : v ∈ A.erase z := (mem_insert.mp hv).resolve_left hvy
      rw [hφ, Function.update_of_ne hvy]
      exact (mem_filter.mp (mem_erase.mp hvA).2).2
  have hpropB : Proper G SB g' := proper_insert_update hg.proper hYmov
  have hintoB : Into SB g' PB := by
    intro v hv
    by_cases hvz : v = z
    · subst hvz; simpa [hg'] using hYPB
    · have hvB : v ∈ B.erase y₁ := (mem_insert.mp hv).resolve_left hvz
      rw [hg', Function.update_of_ne hvz]
      exact hg.into v hvB
  have hS : SA ∪ SB = S := by
    ext v
    constructor
    · intro hv
      rcases mem_union.mp hv with hv | hv
      · rcases mem_insert.mp hv with rfl | hv
        · exact hy₁S
        · exact (mem_filter.mp (mem_erase.mp hv).2).1
      · rcases mem_insert.mp hv with rfl | hv
        · exact hzS
        · exact (mem_filter.mp (mem_erase.mp hv).2).1
    · intro hv
      by_cases hvy : v = y₁
      · subst hvy; exact mem_union_left _ (mem_insert_self _ _)
      by_cases hvz : v = z
      · subst hvz; exact mem_union_right _ (mem_insert_self _ _)
      by_cases hvA : c v ∈ PA
      · exact mem_union_left _ (mem_insert_of_mem (mem_erase.mpr ⟨hvz, mem_filter.mpr ⟨hv, hvA⟩⟩))
      · exact mem_union_right _ (mem_insert_of_mem
          (mem_erase.mpr ⟨hvy, mem_filter.mpr ⟨hv, mem_sdiff.mpr ⟨h.near.into v hv, hvA⟩⟩⟩))
  have hdisj : Disjoint SA SB := by
    rw [disjoint_left]
    intro v hv1 hv2
    rcases mem_insert.mp hv1 with rfl | hv1
    · rcases mem_insert.mp hv2 with e | hv2
      · exact hzy e.symm
      · exact (mem_erase.mp hv2).1 rfl
    · obtain ⟨hvz, hvA⟩ := mem_erase.mp hv1
      rcases mem_insert.mp hv2 with rfl | hv2
      · exact hvz rfl
      · exact (mem_sdiff.mp (mem_filter.mp (mem_erase.mp hv2).2).2).2 (mem_filter.mp hvA).2
  set ψ : V → ℕ := fun v => if v ∈ SA then φ v else g' v with hψ
  have hclsA : ∀ i ∈ PA, cls S ψ i = cls SA φ i := fun i hi =>
    cls_comb_A hintoB hS hPdisj hi
  have hclsB : ∀ i ∈ PB, cls S ψ i = cls SB g' i := fun i hi =>
    cls_comb_B hintoA hS hdisj hPdisj hi
  have hclsW : cls S ψ (c z) = insert y₁ ((cls S c (c z)).erase z) := by
    rw [hclsA _ hWacc, hSA, hφ, cls_insert_update_self, cls_erase', cls_part hWacc]
  have hclsA_ne : ∀ i ∈ PA, i ≠ c z → cls S ψ i = cls S c i := by
    intro i hi hiW
    rw [hclsA i hi, hSA, hφ, cls_insert_update_ne hy₁SA hiW, cls_erase', cls_part hi]
    refine erase_eq_of_notMem fun hm => hiW ?_
    exact (mem_cls.mp hm).2.symm
  have hnear : IsNear G S P ψ s lo Y := by
    refine ⟨proper_comb hpropA hpropB hintoA hintoB hS hPdisj,
      into_comb hintoA hintoB hS hPU, h.near.lo_mem, (mem_sdiff.mp hYPB).1,
      fun e => hYPA (e ▸ h.lo_mem_acc), ?_, ?_, ?_⟩
    · rw [hclsA_ne lo h.lo_mem_acc (Ne.symm hWlo)]; exact h.near.card_lo
    · rw [hclsB Y hYPB, hSB, hg', cls_insert_update_self, card_insert_of_notMem, hg.card Y hYPB]
      exact fun hm => hzSB (mem_cls.mp hm).1
    · intro i hi hilo hiY
      by_cases hiA : i ∈ PA
      · by_cases hiW : i = c z
        · rw [hiW, hclsW, card_insert_of_notMem, card_erase_of_mem (mem_cls.mpr ⟨hzS, rfl⟩),
            hWcard]
          · have : 0 < s := hWcard ▸ card_pos.mpr ⟨z, mem_cls.mpr ⟨hzS, rfl⟩⟩
            omega
          · intro hm
            exact hy₁PA ((mem_cls.mp (mem_erase.mp hm).2).2 ▸ hWacc)
        · rw [hclsA_ne i hiA hiW]
          exact h.near.card i hi hilo (fun e => h.hi_not (e ▸ hiA))
      · have hiB : i ∈ PB := mem_sdiff.mpr ⟨hi, hiA⟩
        rw [hclsB i hiB, hSB, hg', cls_insert_update_ne hzSB hiY]
        exact hg.card i hiB
  -- accessibility
  have hreachA : ∀ X ∈ PA, X ≠ c z → ReflTransGen (Mov G S ψ) X lo := by
    intro X hX hXW
    have hp := reach_restrict h (fun a b hab => hab.1)
      (hterm (c z) hzT X (mem_erase.mpr ⟨hXW, hX⟩))
    refine rtgMono hp fun a b hab => ?_
    obtain ⟨⟨⟨v, hv, hvmov⟩, haW, hbW⟩, haA, hbA⟩ := hab
    refine ⟨v, ?_, ?_⟩
    · rw [hclsA_ne a haA haW]; exact hv
    · intro u hu
      rw [hclsA_ne b hbA hbW] at hu
      exact hvmov u hu
  have hreachW : ReflTransGen (Mov G S ψ) (c z) lo := by
    obtain ⟨j, ⟨w, hw, hwmov⟩, hjW, hjp⟩ := exists_step_avoid (mem_filter.mp hWacc).2 hWlo
    have hjr : ReflTransGen (Mov G S c) j lo := rtgMono hjp fun a b hab => hab.1
    have hjacc : j ∈ PA := by
      have hjP : j ∈ P := by
        by_cases hjl : j = lo
        · rw [hjl]; exact h.near.lo_mem
        · exact mem_palette_of_reach h.near.into (fun a b h => h) hjr hjl
      exact mem_filter.mpr ⟨hjP, hjr⟩
    rw [mem_cls] at hw
    have hwz : w ≠ z := by
      rintro rfl
      exact hnot j hjacc hjW hwmov
    refine ReflTransGen.head ⟨w, ?_, ?_⟩ (hreachA j hjacc hjW)
    · rw [hclsW]; exact mem_insert_of_mem (mem_erase.mpr ⟨hwz, mem_cls.mpr hw⟩)
    · intro u hu
      rw [hclsA_ne j hjacc hjW] at hu
      exact hwmov u hu
  have hsub : PA ⊆ acc G S P ψ lo := by
    intro X hX
    refine mem_filter.mpr ⟨Ctx.acc_subset hX, ?_⟩
    by_cases hXW : X = c z
    · rw [hXW]; exact hreachW
    · exact hreachA X hX hXW
  have hy₂B' : y₂ ∈ B.erase y₁ := mem_erase.mpr ⟨hne.symm, hy₂B⟩
  have hZPB : g y₂ ∈ PB := hg.into y₂ hy₂B'
  have hy₂z : y₂ ≠ z := by rintro rfl; exact hzB hy₂B
  have hZ : g y₂ ∈ acc G S P ψ lo := by
    refine mem_filter.mpr ⟨(mem_sdiff.mp hZPB).1, ReflTransGen.head ⟨y₂, ?_, ?_⟩ hreachW⟩
    · rw [hclsB _ hZPB, hSB, hg']
      exact mem_cls.mpr ⟨mem_insert_of_mem hy₂B', by rw [Function.update_of_ne hy₂z]⟩
    · intro u hu hadj
      rw [hclsW] at hu
      rcases mem_insert.mp hu with rfl | hu
      · exact hnadj hadj.symm
      · obtain ⟨huz, hu⟩ := mem_erase.mp hu
        exact huz (solo_eq hsolo₂ (mem_cls.mp hu).1 (mem_cls.mp hu).2 hadj)
  refine ⟨ψ, Y, hnear, ?_⟩
  have hc := card_le_card (insert_subset hZ hsub)
  rw [card_insert_of_notMem (mem_sdiff.mp hZPB).2] at hc
  omega

end HajnalSzemeredi
