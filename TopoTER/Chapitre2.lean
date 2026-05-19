import TopoTER.Chapitre1

open TER

-- 2. Espaces topologiques

-- Définition 2.1.

open Set

class EspTop (X : Type*) where
  est_ouvert : Set X → Prop
  univ_ouvert : est_ouvert Ω
  empty_ouvert : est_ouvert ∅
--
  union_ouvert {F : Famille X} (hu : ∀ A ∈ F, est_ouvert A) :
    est_ouvert (⋃ᵢ F)
--
  inter_ouvert {u v : Set X} (hu : est_ouvert u) (hv : est_ouvert v) :
    est_ouvert (u ∩ v)

attribute [simp] EspTop.univ_ouvert EspTop.empty_ouvert

variable {X Y : Type*} [EspTop X] [EspTop Y]

namespace EspTop

lemma iunion_ouvert {ι : Type u_1} {u : ι → Set X} (h : ∀ i, est_ouvert (u i)) :
  est_ouvert (⋃ i, u i) := by
  let F : Famille X := ⟨ι, u⟩
  have eq : ⋃ᵢ F = ⋃ i, u i := by rfl
  rw [←eq]; apply union_ouvert; intro A hA
  rcases hA with ⟨i, hi⟩; rw [←hi]; exact h i

lemma bunion_ouvert {ι : Type u_1} {u : ι → Set X} {I : Set ι} (h : ∀ i ∈ I,
  est_ouvert (u i)) : est_ouvert (⋃ i ∈ I, u i) := by
  apply iunion_ouvert; intro i
  by_cases hi : i ∈ I
  · simp [hi, h]
  · simp only [hi, iUnion_of_empty]
    exact empty_ouvert

lemma union_est_ouvert (u v : Set X) (hu : est_ouvert u) (hv : est_ouvert v) :
  est_ouvert (u ∪ v) := by
  let P : Set (Set X) := {u, v}
  have union_F : ⋃ x ∈ P, x = u ∪ v := by
    ext x; simp only [mem_iUnion, exists_prop]
    apply Iff.intro
    · case mp => intro h; rcases h with ⟨s, hs, x_in⟩
                 cases hs; repeat simp_all
    · case mpr => intro h; cases h
                  · case inl => use u, Or.inl (refl u)
                  · case inr => use v, Or.inr (refl v)
--
  rw [←union_F]; apply bunion_ouvert; intro s hs
  cases hs; repeat simp_all

lemma inter_fini_ouvert {ι : Type} {u : ι → Set X} {I : Set ι} [hI : Finite I]
  (h : ∀ i ∈ I, est_ouvert (u i)) : est_ouvert (⋂ i ∈ I, u i) := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | @insert x s hs hx H =>
      rw [biInter_insert x s u]
      apply inter_ouvert
      · apply h; exact mem_insert x s
      · apply H; intro i hi; apply h
        exact mem_insert_of_mem x hi

lemma inter_fini_ouvert' {ι : Type} {u : ι → Set X} [Finite ι] (h : ∀ i,
  est_ouvert (u i)) : est_ouvert (⋂ i, u i) := by
  have eq : ⋂ i ∈ Ω, u i = ⋂ i, u i := by simp
  rw [←eq]; apply inter_fini_ouvert (I := Ω); intro i hi; exact h i

@[simp] def est_ferme (s : Set X) := est_ouvert sᶜ

lemma est_ouvert_iff_compl_est_ferme {s : Set X} : est_ouvert s ↔ est_ferme sᶜ
  := by rw [est_ferme, compl_compl]

@[simp] lemma univ_est_ferme : est_ferme (univ : Set X) := by
  rw [est_ferme, compl_univ]
  exact empty_ouvert

@[simp] lemma empty_est_ferme : est_ferme (∅ : Set X) := by
  rw [est_ferme, compl_empty]
  exact univ_ouvert

lemma inter_ferme {F : Famille X} (hu : ∀ A ∈ F, est_ferme A) :
  est_ferme (⋂ᵢ F) := by
  rw [est_ferme, inter_famille_compl]
  apply union_ouvert; intro A hA; rw [in_compl_famille] at hA
  rw [est_ouvert_iff_compl_est_ferme]; apply hu Aᶜ hA

lemma union_ferme {u v : Set X} (hu : est_ferme u) (hv : est_ferme v) :
  est_ferme (u ∪ v) := by
  rw [est_ferme, compl_union]
  apply inter_ouvert; repeat assumption

lemma inter_est_ferme {ι : Type u_1} {u : ι → Set X} (hu : ∀ i, est_ferme (u i)) :
  est_ferme (⋂ i, u i) := by
  rw [est_ferme, compl_iInter]
  exact iunion_ouvert hu

lemma union_fini_ferme {ι : Type} {u : ι → Set X} {I : Set ι} [Finite I]
  (h : ∀ i ∈ I, est_ferme (u i)) : est_ferme (⋃ i ∈ I, u i) := by
  rw [est_ferme, compl_iUnion₂]
  exact inter_fini_ouvert h

lemma union_fini_ferme' {ι : Type} {u : ι → Set X} [Finite ι]
  (h : ∀ i, est_ferme (u i)) : est_ferme (⋃ i, u i) := by
  rw [est_ferme, compl_iUnion]
  exact inter_fini_ouvert' h

-- Exemple 2.2.

-- a)

open Metrique
instance {X : Type*} [EspaceMetrique X] : EspTop X where
  est_ouvert := A ↦ ouverte A
  univ_ouvert := ouverte_of_uni
  empty_ouvert := ouverte_of_vide

  union_ouvert := ouverte_of_union
  inter_ouvert := ouverte_of_inter

-- 2.2. Intérieur, adhérence, voisinage

structure est_vois_ouv_dans {X : Type*} [EspTop X] (x : X) (s ouv : Set X) where
  x_dans : x ∈ ouv
  ouv_ouvert : est_ouvert ouv
  ouv_contenu : ouv ⊆ s

def est_vois {X : Type*} [EspTop X] (x : X) (s : Set X) :=
  ∃ u, est_vois_ouv_dans x s u

lemma ouvert_ssi_vois (s : Set X) : est_ouvert s ↔ ∀ x ∈ s, est_vois x s := by
  apply Iff.intro
  · case mp => intro h x hx; use s
               exact ⟨hx, h, subset_refl s⟩
  · case mpr =>
      intro h; choose! u hu using h
      have union : s = ⋃ x ∈ s, u x := by
        ext x; simp only [mem_iUnion, exists_prop]
        apply Iff.intro
        · intro hx; use x; apply And.intro hx
          exact ((hu x) hx).x_dans
        · intro h; rcases h with ⟨i, hi, hx⟩
          specialize hu i hi; exact hu.ouv_contenu hx
      rw [union]; apply bunion_ouvert; intro x x_in
      exact (hu x x_in).ouv_ouvert

@[simp] def adh (s : Set X) := {x | ∀ u, est_vois x u → (u ∩ s).Nonempty}

lemma contenu_adh (s : Set X) : s ⊆ adh s := by
  intro x hx U hxU
  use x
  constructor
  · rcases hxU with ⟨V, hV⟩
    apply hV.ouv_contenu
    exact hV.x_dans
  exact hx

lemma adh_eq_inter (s : Set X) : adh s = ⋂₀ {F : Set X | est_ferme F ∧ s ⊆ F} := by
  apply Subset.antisymm_iff.mpr
  constructor
  · intro x hasx F hF
    simp only [mem_setOf_eq, est_ferme] at hF; rcases hF with ⟨hF1, hF2⟩;
    by_contra hxnh; rw[← mem_compl_iff] at hxnh; rw[ouvert_ssi_vois] at hF1; specialize hF1 x hxnh;
    specialize hasx (Fᶜ) hF1
    have subs_nempty : (Fᶜ ∩ s) ⊆ Fᶜ ∩ F := inter_subset_inter_right (Fᶜ) hF2
    have hne : (Fᶜ ∩ F).Nonempty := Nonempty.mono subs_nempty hasx
    rw[nonempty_iff_ne_empty, inter_comm] at hne
    exact hne (inter_compl_self F)
  rintro x hx U ⟨V, ⟨h1, h2, h3⟩⟩
  have HVUS : V ∩ s ⊆ U ∩ s := by exact inter_subset_inter_left s h3
  apply Nonempty.mono HVUS
  by_contra! h;
  have hVc : est_ferme Vᶜ := est_ouvert_iff_compl_est_ferme.mp h2
  rw[← Set.subset_empty_iff, ← Set.disjoint_iff, ← subset_compl_iff_disjoint_left] at h
  have : x ∈ Vᶜ := by
    apply hx
    exact mem_sep hVc h
  exact this h1

lemma adh_ferme (s : Set X) : est_ferme (adh s) := by
  rw [adh_eq_inter, sInter_eq_iInter]
  apply inter_est_ferme
  intro F
  exact F.property.1

----------------------------------------------------------------------------------------------
@[simp]
def int (s : Set X) := {x | est_vois x s}

lemma ouvert_iff_int (U : Set X) : est_ouvert U ↔ (int U) = U := by
  constructor
  · intro hU
    unfold int
    ext x
    constructor
    · intro hx
      rcases hx with ⟨_,⟨h1, _, h2⟩⟩
      exact mem_of_subset_of_mem h2 h1
    · exact fun hx ↦ ⟨U, hx, hU, by simp⟩
  rw [ouvert_ssi_vois]
  intro h x hx
  rw [<-h] at hx
  unfold int at hx
  exact hx

@[simp]
def front (s : Set X) := (adh s)\(int s)

lemma front_carac (U : Set X) : front U = (adh U) ∩ (adh (Uᶜ)) := by
  unfold front
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    constructor
    · exact hx1
    · simp only [adh, mem_setOf_eq]
      intro V hV
      by_contra h
      absurd hx2
      rcases hV with ⟨v, x_dans, ouv_ouvert, ouv_contenu⟩
      use v
      constructor
      · exact x_dans
      · exact ouv_ouvert
      · rw [inter_compl_nonempty_iff] at h
        push_neg at h
        apply subset_trans ouv_contenu h
  · rintro ⟨hx1, hx2⟩
    constructor
    · exact hx1
    · simp only [int, mem_setOf_eq]
      by_contra! h
      specialize hx2 U h
      rw [inter_comm, compl_inter_self U] at hx2
      choose y hy using hx2
      exact hy

structure base_de_vois {X : Type*} [EspTop X] (x : X) {ι : Type} (V : ι → Set X) where
  V_vois : ∀(i : ι), est_vois x (V i)
  V_base : ∀(W : Set X), est_vois x W → ∃(i : ι), (V i) ⊆ W

-- 2.3. Suites dans un espace topologique ou métrique

class EspSepareT2 (X : Type*) extends EspTop X where
  est_separe : ∀ (x y : X), x ≠ y → ∃ (U V : Set X),
    (est_ouvert U) ∧ (est_ouvert V) ∧ (x ∈ U) ∧ (y ∈ V) ∧ (U ∩ V = ∅)

instance {X : Type*} [M : EspaceMetrique X] : EspSepareT2 X where
  est_separe := by
    intro x y h; let d := d(x, y) / 2
    have d_pos : d > 0 := by
      apply half_pos; apply lt_of_le_of_ne
      · exact M.is_dist.nneg x y
      · intro eq; apply h; rw [←M.is_dist.sep, eq]
--
    let B1 := Bₒ x d; let B2 := Bₒ y d
    use B1, B2, ouv_of_boule_ouv x d, ouv_of_boule_ouv y d,
            centre_in_boule x d_pos, centre_in_boule y d_pos
    apply eq_empty_of_forall_notMem; intro z hz
    have ineq₁ : d(z, x) < d := hz.left
    have ineq₂ : d(z, y) < d := hz.right
    have ineq₃ := M.is_dist.ineq x z y
    rw [M.is_dist.symm] at ineq₁
    unfold d at ineq₁; unfold d at ineq₂; linarith

def dense (X : Type*) [EspTop X] (A : Set X) : Prop := adh A = univ

lemma dense_iff_inter_ouvert_nonempty (s : Set X) :
dense X s ↔ ∀ V, est_ouvert V → V.Nonempty → (V ∩ s).Nonempty := by
  constructor
  · rintro s_dens V V_ouv ⟨x, hxV⟩
    have hxs : x ∈ (adh s) := by
      rw [s_dens]
      exact mem_univ x
    have V_vois : est_vois x V := ⟨V, hxV, V_ouv, fun y hy ↦ hy⟩
    exact hxs V V_vois
  · intro h
    unfold dense
    apply Subset.antisymm_iff.mpr
    constructor
    · exact (fun x _ ↦ mem_univ x)
    · rintro x _ u ⟨v, ⟨x_in_v, v_ouv, v_in_u⟩⟩
      have v_ne : v.Nonempty := by use x
      specialize h v v_ouv v_ne
      exact Nonempty.mono (inter_subset_inter_left s v_in_u) h

end EspTop
