import TopoTER.Chapitre2

open TER Set EspTop Metrique

variable {X Z : Type*} [EspTop X] [EspTop Z]
variable {Y : Type*} [EspSepareT2 Y]
variable {E F : Type*} [EspaceMetrique E] [EspaceMetrique F]

def est_continu_point {X Y : Type*} [EspTop X] [EspTop Y] (f : X → Y) (x : X) : Prop :=
  ∀(V : Set Y), (est_vois (f x) V) → ∃(U : Set X), (est_vois x U) ∧  (f '' U ⊆ V)

def est_continu {X Y : Type*} [EspTop X] [EspTop Y] (f : X → Y) : Prop :=
  ∀(x : X), est_continu_point f x

theorem continu_iff_preim_ouv (f : X → Y) :
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
    rcases h with ⟨W, ⟨U, xU, Uouv, UinW⟩, fWinU⟩
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

theorem continu_ouv_ferm (f : X → Y) : (∀ (V : Set Y),
(est_ouvert V → est_ouvert (f ⁻¹' V)))  ↔ (∀(F : Set Y), est_ferme F → est_ferme (f ⁻¹' F)) := by
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

theorem continu_iff_preim_ferm (f : X → Y) :
est_continu f ↔ ∀ (F : Set Y), est_ferme F → est_ferme (f ⁻¹' F) := by
  rw[continu_iff_preim_ouv]
  exact continu_ouv_ferm f

lemma continu_im_adh_in_adh_im (f : X → Y) (A : Set X) :
est_continu f → f '' (adh A) ⊆ adh (f '' A) := by
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

def lipschitz (k : ℝ) (f : E → F) := ∀ x y, d(f x, f y) ≤ k * d(x, y)

def unif_continu (f : E → F) := ∀ ε > 0, ∃ δ > 0, ∀(x y : E), d(x, y) ≤ δ → d(f x, f y) ≤ ε

def k_lipschitz (f : E → F) := ∃ k, lipschitz k f

open Set.Notation

-- lire l'intro de Mathlib.Data.Set.Subset

instance toto (s : Set X) : EspTop s where
  est_ouvert := fun u ↦ ∃ v : Set X, est_ouvert v ∧ u = s ↓∩ v
  univ_ouvert := ⟨univ, ⟨univ_ouvert, by simp⟩⟩
  empty_ouvert := ⟨∅, ⟨empty_ouvert, by simp⟩⟩
  union_ouvert := by
    intro F h; sorry
  inter_ouvert := by
    rintro u v ⟨U, ⟨Uouv, hU⟩⟩ ⟨V, ⟨Vouv, hV⟩⟩
    use U ∩ V
    constructor
    · exact inter_ouvert Uouv Vouv
    · rw [hU, hV]; simp

def est_ouvert_elementaire (s : Set (X × X)) :=
  ∃ U1 U2 : Set X, (s = (U1 × U2)) ∧ (est_ouvert U1) ∧ (est_ouvert U2)

instance top_prod {ι : Type}{u : ι → Set (X × X)} : EspTop (X × X) where
  est_ouvert := fun w ↦ (w = ⋂ i, u i) ∧ (∀ i, est_ouvert_elementaire (u i))
  univ_ouvert := sorry
  empty_ouvert := sorry

  union_ouvert := sorry
  inter_ouvert := sorry
