import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic

open Set

class EspTop (X : Type) where
  est_ouvert : Set X → Prop
  univ_ouvert : est_ouvert univ
  empty_ouvert : est_ouvert ∅
  union_ouvert {ι : Type} {u : ι → Set X} (hu : ∀ i, est_ouvert (u i)) : est_ouvert (⋃ i, u i)
  inter_ouvert {u v : Set X} (hu : est_ouvert u) (hv : est_ouvert v) : est_ouvert (u ∩ v)

attribute [simp] EspTop.univ_ouvert EspTop.empty_ouvert

variable {X : Type} [EspTop X]

open EspTop

lemma EspTop.bunion_ouvert {ι : Type} {u : ι → Set X} {I : Set ι} (h : ∀ i ∈ I, est_ouvert (u i)) : est_ouvert (⋃ i ∈ I, u i) := by
  apply union_ouvert
  intro i
  by_cases hi : i ∈ I
  · simp [hi, h]
  · simp only [hi, iUnion_of_empty]
    exact empty_ouvert

lemma EspTop.inter_fini_ouvert {ι : Type} {u : ι → Set X} {I : Set ι} (hI : I.Finite)
  (h : ∀ i ∈ I, est_ouvert (u i)) : est_ouvert (⋂ i ∈ I, u i) := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp;
  | @insert x s hs hx H =>
    rw [biInter_insert x s u]
    apply inter_ouvert
    · apply h
      · apply mem_insert
    apply H
    intro i hi
    apply h
    apply mem_insert_of_mem
    exact hi

lemma EspTop.inter_fini_ouvert' {ι : Type} {u : ι → Set X} [Finite ι]
    (h : ∀ i, est_ouvert (u i)) : est_ouvert (⋂ i, u i) := by
  simpa using inter_fini_ouvert finite_univ fun i _ ↦ h i

structure est_vois_ouv_dans {X : Type} [EspTop X] (x : X) (s ouv : Set X) where
  x_dans : x ∈ ouv
  ouv_ouvert : est_ouvert ouv
  ouv_contenu : ouv ⊆ s

def est_vois {X : Type} [EspTop X] (x : X) (s : Set X) :=
  ∃ u, est_vois_ouv_dans x s u

lemma ouvert_ssi_vois (s : Set X) : est_ouvert s ↔ ∀ x ∈ s, est_vois x s := by
  constructor
  · intro h x hx
    use s
    constructor
    · exact hx
    · exact h
    · rfl
  · intro h
    choose! u hu using h
    have : s = ⋃ x ∈ s, u x := by
      · apply Subset.antisymm_iff.mpr
        constructor
        · intro x hx
          · simp only [mem_iUnion, exists_prop]
            use x
            constructor
            · exact hx
            specialize hu x
            have : est_vois_ouv_dans x s (u x) := by exact hu hx
            exact this.x_dans
        simp only [iUnion_subset_iff]
        intro i hi
        specialize hu i hi
        exact hu.ouv_contenu
    rw [this]
    apply bunion_ouvert
    intro j hj
    specialize hu j hj
    exact hu.ouv_ouvert




def est_fermé (s : Set X) := est_ouvert sᶜ

lemma EspTop.est_ouvert.compl_est_fermé {s : Set X} (h : est_ouvert s) : est_fermé sᶜ := by
  simp only [est_fermé]
  rw[compl_compl]
  exact h

@[simp]
lemma EspTop.univ_est_fermé : est_fermé (univ : Set X) := by
  simp only [est_fermé]
  rw[compl_univ]
  apply empty_ouvert

@[simp]
lemma EspTop.empty_est_fermé : est_fermé (∅ : Set X) := by
  simp only [est_fermé]
  rw[compl_empty]
  apply univ_ouvert

lemma EspTop.union_est_fermé {u v : Set X} (hu : est_fermé u) (hv : est_fermé v) :
    est_fermé (u ∪ v) := by
    simp only [est_fermé]
    rw[compl_union]
    apply inter_ouvert
    · exact hu
    · exact hv

lemma EspTop.inter_est_fermé {ι : Type} {u : ι → Set X} (hu : ∀ i, est_fermé (u i)) :
    est_fermé (⋂ i, u i) := by
    simp only [est_fermé]
    rw [compl_iInter]
    apply union_ouvert
    exact hu


lemma EspTop.union_fini_fermé {ι : Type} {u : ι → Set X} {I : Set ι} (hI : I.Finite)
    (h : ∀ i ∈ I, est_fermé (u i)) : est_fermé (⋃ i ∈ I, u i) := by
      simp only [est_fermé] at *
      rw[compl_iUnion₂]
      exact inter_fini_ouvert hI h

lemma EspTop.inter_fini_fermé' {ι : Type} {u : ι → Set X} [Finite ι]
    (h : ∀ i, est_fermé (u i)) : est_fermé (⋃ i, u i) := by
    simp only [est_fermé] at *
    rw [compl_iUnion]
    exact inter_fini_ouvert' h

def adh (s : Set X) := {x | ∀ u, est_vois x u → (u ∩ s).Nonempty }

lemma contenu_adh (s : Set X) : s ⊆ adh s := by
  intro x hx U hxU
  use x
  constructor
  · rcases hxU with ⟨hux, h⟩
    apply h.ouv_contenu
    exact h.x_dans
  exact hx

lemma adh_eq_inter (s : Set X) : adh s = ⋂₀ {F : Set X | est_fermé F ∧ s ⊆ F} := by
  apply Subset.antisymm_iff.mpr
  constructor
  · intro x hasx h hF
    simp only [mem_setOf_eq] at hF; rcases hF with ⟨hF1, hF2⟩; simp only [est_fermé] at hF1
    by_contra hxnh; rw[← mem_compl_iff] at hxnh; rw[ouvert_ssi_vois] at hF1; specialize hF1 x hxnh;
    specialize hasx (hᶜ) hF1
    have subs_empty : (hᶜ ∩ s) ⊆ hᶜ ∩ h := by exact inter_subset_inter (fun _ a_1 ↦ a_1) hF2
    have hne : (hᶜ ∩ h).Nonempty := by
      rcases hasx with ⟨elt, helt⟩
      use elt
      apply subs_empty helt
    rw[nonempty_iff_ne_empty] at hne
    rw[inter_comm] at hne
    apply hne (inter_compl_self h)
  intro x hx U hxU
  rcases hxU with ⟨V, hxVU⟩
  rcases hxVU with ⟨h1, h2, h3⟩
  have HVUS : V ∩ s ⊆ U ∩ s := by exact inter_subset_inter h3 fun a a_1 ↦ a_1
  apply Nonempty.mono HVUS
  by_contra h; rw[nonempty_iff_ne_empty] at h; push_neg at h
  have hVc : est_fermé Vᶜ := by exact est_ouvert.compl_est_fermé h2
  rw[← Set.subset_empty_iff, ← Set.disjoint_iff, ← subset_compl_iff_disjoint_left] at h
  have : x ∈ Vᶜ := by
    apply hx
    exact mem_sep hVc h
  apply this h1
