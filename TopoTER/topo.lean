import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Notation

open Set

class EspTop (X : Type) where
  est_ouvert : Set X → Prop
  univ_ouvert : est_ouvert univ
  empty_ouvert : est_ouvert ∅
  union_ouvert {ι : Type} {u : ι → Set X} (hu : ∀ i, est_ouvert (u i)) : est_ouvert (⋃ i, u i)
  inter_ouvert {u v : Set X} (hu : est_ouvert u) (hv : est_ouvert v) : est_ouvert (u ∩ v)

attribute [simp] EspTop.univ_ouvert EspTop.empty_ouvert

variable {X} {α : Type} [EspTop X]
variable {Y} {β : Type} [EspTop Y]

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
    repeat assumption
    simp
  · intro h
    choose! u hu using h
    have : s = ⋃ x ∈ s, u x := by
      apply Subset.antisymm_iff.mpr
      constructor
      · intro x hx
        · simp only [mem_iUnion, exists_prop]
          use x
          exact ⟨hx, ((hu x) hx).x_dans⟩
      simp only [iUnion_subset_iff]
      intro i hi
      specialize hu i hi
      exact hu.ouv_contenu
    rw [this]
    apply bunion_ouvert
    intro j hj
    exact (hu j hj).ouv_ouvert

def est_ferme (s : Set X) := est_ouvert sᶜ

lemma EspTop.est_ouvert_iff_compl_est_ferme {s : Set X} : est_ouvert s ↔ est_ferme sᶜ := by
  simp only [est_ferme]
  rw[compl_compl]

@[simp]
lemma EspTop.univ_est_ferme : est_ferme (univ : Set X) := by
  simp only [est_ferme]
  rw[compl_univ]
  exact empty_ouvert

@[simp]
lemma EspTop.empty_est_ferme : est_ferme (∅ : Set X) := by
  simp only [est_ferme]
  rw[compl_empty]
  exact univ_ouvert

lemma EspTop.union_est_ferme {u v : Set X} (hu : est_ferme u) (hv : est_ferme v) :
    est_ferme (u ∪ v) := by
  simp only [est_ferme]
  rw[compl_union]
  apply inter_ouvert
  <;> assumption

lemma EspTop.inter_est_ferme {ι : Type} {u : ι → Set X} (hu : ∀ i, est_ferme (u i)) :
    est_ferme (⋂ i, u i) := by
  simp only [est_ferme]
  rw [compl_iInter]
  exact union_ouvert hu

lemma EspTop.union_fini_ferme {ι : Type} {u : ι → Set X} {I : Set ι} (hI : I.Finite)
    (h : ∀ i ∈ I, est_ferme (u i)) : est_ferme (⋃ i ∈ I, u i) := by
  simp only [est_ferme] at *
  rw[compl_iUnion₂]
  exact inter_fini_ouvert hI h

lemma EspTop.inter_fini_ferme' {ι : Type} {u : ι → Set X} [Finite ι]
    (h : ∀ i, est_ferme (u i)) : est_ferme (⋃ i, u i) := by
  simp only [est_ferme] at *
  rw [compl_iUnion]
  exact inter_fini_ouvert' h

def adh (s : Set X) := {x | ∀ u, est_vois x u → (u ∩ s).Nonempty}

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
  by_contra! h; --rw[nonempty_iff_ne_empty] at h; push_neg at h
  have hVc : est_ferme Vᶜ := est_ouvert_iff_compl_est_ferme.mp h2
  rw[← Set.subset_empty_iff, ← Set.disjoint_iff, ← subset_compl_iff_disjoint_left] at h
  have : x ∈ Vᶜ := by
    apply hx
    exact mem_sep hVc h
  exact this h1

----------------------------------------------------------------------------------------------

def int (s : Set X) := {x | est_vois x s}

def front (s : Set X) := (adh s)\(int s)

structure base_de_vois {X : Type} [EspTop X] (x : X) {ι : Type} (V : ι → Set X) where
  V_vois : ∀(i : ι), est_vois x (V i)
  V_base : ∀(W : Set X), est_vois x W → ∃(i : ι), (V i) ⊆ W

--def est_separe {X : Type} [EspTop X] : Prop :=
--  ∀ (x y : X), x ≠ y → ∃ (U V : Set X),
--  (est_ouvert U) ∧ (est_ouvert V) ∧ (x ∈ U) ∧ (y ∈ V) ∧ (U ∩ V = ∅)


class EspSepareT2 (X : Type) extends EspTop X where
  est_separe : ∀ (x y : X), x ≠ y → ∃ (U V : Set X),
  (est_ouvert U) ∧ (est_ouvert V) ∧ (x ∈ U) ∧ (y ∈ V) ∧ (U ∩ V = ∅)

variable {X : Type} [EspTop X]
variable {Y : Type} [EspSepareT2 Y]

def est_continu_point {X Y: Type} [EspTop X] [EspTop Y] (f : X → Y) (x : X): Prop :=
  ∀(V : Set Y), (est_vois (f x) V) → ∃(U : Set X), (est_vois x U) ∧  (f '' U ⊆ V)

def est_continu {X Y: Type} [EspTop X] [EspTop Y] (f : X → Y): Prop :=
  ∀(x : X), est_continu_point f x

theorem continu_iff_preim_ouv (f : X → Y):
  est_continu f ↔ ∀ (V : Set Y), est_ouvert V → est_ouvert (f ⁻¹' V) := by
  constructor
  · intro h V Vouv
    rw [ouvert_ssi_vois]
    intro x hx
    have fxV : f x ∈ V := hx
    have Vvoisfx : est_vois (f x) V := by
      constructor
      constructor; exact fxV; exact Vouv; rfl
    specialize h x
    specialize h V Vvoisfx
    rcases h with ⟨W, ⟨⟨U, xU, Uouv, UinW⟩, fWinU⟩⟩
    use U
    constructor
    · exact xU
    · exact Uouv
    · rw [<-image_subset_iff]
      trans f '' W; exact image_mono UinW; exact fWinU
  · intro h x W Wvois
    rcases Wvois with ⟨V, fxV, Vouv, VinW⟩
    have fxV : x ∈ f ⁻¹' V := fxV
    have fVouv : est_ouvert (f ⁻¹' V) := h V Vouv
    use (f ⁻¹' V)
    constructor
    · use (f ⁻¹' V)
      exact ⟨fxV, fVouv, by rfl⟩
    · trans V; simp; exact VinW

theorem continu_ouv_ferm (f : X → Y) : (∀ (V : Set Y), (est_ouvert V → est_ouvert (f ⁻¹' V)))  ↔ (∀(F : Set Y), est_ferme F → est_ferme (f ⁻¹' F)) := by
  constructor
  · intro h V hV
    --unfold est_ferme at *
    specialize h Vᶜ hV
    rw[preimage_compl] at h
    exact h
  · intro h V hV
    rw[est_ouvert_iff_compl_est_ferme] at *
    specialize h Vᶜ hV
    rw[preimage_compl] at h
    exact h

theorem continu_iff_preim_ferm (f : X → Y) : est_continu f ↔ ∀ (F : Set Y), est_ferme F → est_ferme (f ⁻¹' F) := by
  rw[continu_iff_preim_ouv]
  exact continu_ouv_ferm f

lemma continu_im_adh_in_adh_im (f : X → Y) (A : Set X) : est_continu f → f '' (adh A) ⊆ adh (f '' A) := by
  intro h y hy V hV
  rw [mem_image] at hy
  rcases hy with ⟨x, ⟨hx, yeqfx⟩⟩
  specialize h x
  rw [<-yeqfx] at hV
  specialize h V hV
  rcases h with ⟨U, ⟨hU, fUinV⟩⟩
  specialize hx U hU
  rcases hx with ⟨x', ⟨hx'U, hx'A⟩⟩
  use f x'
  constructor
  · apply fUinV
    exact mem_image_of_mem f hx'U
  · exact mem_image_of_mem f hx'A

open Set.Notation

-- lire l'intro de Mathlib.Data.Set.Subset

instance (s : Set X) : EspTop s where
  est_ouvert := fun u ↦ ∃ v : Set X, est_ouvert v ∧ u = s ↓∩ v
  univ_ouvert := ⟨univ, ⟨univ_ouvert, by simp⟩⟩
  empty_ouvert := ⟨∅, ⟨empty_ouvert, by simp⟩⟩
  union_ouvert := by
    intro I u h
    choose v hv using h
    use ⋃ i, v i
    constructor; exact union_ouvert (fun i ↦ (hv i).1); ext x; simp [hv]
  inter_ouvert := by
    rintro u v ⟨U, ⟨Uouv, hU⟩⟩ ⟨V, ⟨Vouv, hV⟩⟩
    use U ∩ V
    constructor
    · exact inter_ouvert Uouv Vouv
    · rw [hU, hV]; simp

def dense (X : Type) [EspTop X] (A : Set X) : Prop := adh A = X

def prop_baire {X : Type} [EspTop X] (u : ℕ → Set X) : Prop := (∀ (n : ℕ), dense X (u n)) → dense X (⋂ n : ℕ, u n)

def baire (X : Type) [EspTop X] : Prop := ∀ (u : ℕ → Set X), prop_baire u

lemma baire_ouvert (h : baire X) (v : Set X) : est_ouvert v → (baire v) := by
  intro hv u h
  unfold dense
  have vinadh : ∀ (n : ℕ), v ⊆ adh (↑(u n)) := by
    intro n
    specialize h n
    unfold dense at h
    intro x hx
    intro w hw
    rw [inter_nonempty]
    use x
    constructor
    · rcases hw with ⟨U, ⟨h1, _, h2⟩⟩
      exact h2 h1
    · sorry
--  have adhv : ∀ (n : ℕ), adh (u n) = adh v := by
--    intro n
--    specialize h n
  sorry

inductive is_open_in_top_gen (S : Set (Set X)) : Set X → Prop
| base_top {U} (h : U ∈ S) : is_open_in_top_gen S U
| univ : is_open_in_top_gen S univ
| empty : is_open_in_top_gen S ∅
| Inter (U V : Set X) : is_open_in_top_gen S U → is_open_in_top_gen S V →
    is_open_in_top_gen S (U ∩ V)
| Union {ι : Type} {u : ι → Set X} :
  (∀ i , is_open_in_top_gen S (u i)) → is_open_in_top_gen S (⋃ i, u i)


def topo_engendree (S : Set (Set X)) : EspTop X where
  est_ouvert := is_open_in_top_gen S
  univ_ouvert := is_open_in_top_gen.univ
  empty_ouvert := is_open_in_top_gen.empty
  union_ouvert := is_open_in_top_gen.Union
  inter_ouvert := by exact fun {u v} hu hv ↦ is_open_in_top_gen.Inter u v hu hv

structure base_topo (S : Set (Set X)) : Prop where
  Union_univ : ⋃₀ S = univ
  base_inter : ∀ b₁ ∈ S, ∀ b₂ ∈ S, ∀ x ∈ b₁ ∩ b₂, ∃ b ∈ S, x ∈ b ∧ b ⊆ b₁ ∩ b₂
