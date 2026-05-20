import TopoTER.Chapitre2

open TER Set EspTop Metrique

variable {X Z : Type*} [EspTop X] [EspTop Z]
variable {Y : Type*} [EspSepareT2 Y]
variable {E F : Type*} [M : EspaceMetrique E] [EspaceMetrique F]

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

def unif_continu (f : E → F) := ∀ ε > 0, ∃ δ > 0, ∀(x y : E), d(x, y) < δ → d(f x, f y) < ε

def lipschitz (k : ℝ) (f : E → F) := ∀ x y, d(f x, f y) ≤ k * d(x, y)

def k_lipschitz (f : E → F) := ∃ k > 0, lipschitz k f

lemma unif_continu_cont (f : E → F) : unif_continu f → est_continu f := by
  intro hucf
  unfold est_continu
  unfold unif_continu at hucf
  intro x G hG
  rcases hG with ⟨V, hxV, Vouv, V_G⟩
  specialize Vouv (f x) hxV
  rcases Vouv with ⟨r , ⟨hr_pos, hBr⟩⟩
  let ε : ℝ := r/3
  have ε_pos : ε > 0 :=
  calc
    ε = r/3 := by rfl
    _ > 0 := by linarith
  specialize hucf ε ε_pos
  rcases hucf with ⟨δ, ⟨hδ_pos, hf⟩⟩
  use Bₒ x (δ/2)
  constructor
  · apply ouv_est_vois (ouv_of_boule_ouv x (δ/2)) (centre_in_boule x (by linarith))
  · rw [Set.image_subset_iff]
    intro y hyB

    have y_dist : d(x, y) < δ := by
      simp only [boule_ouverte] at hyB
      rw[Set.mem_setOf] at hyB
      trans δ/2
      · rw[EspaceMetrique.is_dist.symm x y];
        exact hyB
      · linarith

    specialize hf x y y_dist

    have fy_in_boule : (f y) ∈ Bₒ (f x) r := by
      dsimp
      trans ε
      · rw[EspaceMetrique.is_dist.symm (f y) (f x)]; exact hf
      · calc
          ε = r/3 := by rfl
          _  < r := by linarith
    rw[Set.mem_preimage]
    exact mem_preimage.mp (V_G (hBr fy_in_boule))

lemma lip_continu (f : E → F) : k_lipschitz f → unif_continu f := by
  unfold k_lipschitz unif_continu
  rintro hlip ε ε_pos
  rcases hlip with ⟨k, hk_pos, hk⟩
  unfold lipschitz at hk
  use ε/(2*k)
  constructor
  · calc
      ε/(2*k) = ε/2 * 1/k := by ring
      _ > 0 := by apply mul_pos; linarith; apply inv_pos_of_pos hk_pos
  intro x y hxy
  calc
    EspaceMetrique.d (f x) (f y) ≤ k * EspaceMetrique.d x y := by specialize hk x y; exact hk
    _ < k * (ε/(2*k)) := by exact mul_lt_mul_of_pos_left hxy hk_pos
    _ = ε/2 := by field
    _ < ε := by linarith


open Set.Notation

-- lire l'intro de Mathlib.Data.Set.Subset

instance induite (s : Set X) : EspTop s where
  est_ouvert := fun u ↦ ∃ v : Set X, est_ouvert v ∧ u = s ↓∩ v
  univ_ouvert := ⟨univ, ⟨univ_ouvert, by simp⟩⟩
  empty_ouvert := ⟨∅, ⟨empty_ouvert, by simp⟩⟩
  union_ouvert := by
    intro I u h
    choose v hv using h
    use ⋃ i, v i
    constructor
    · exact union_ouvert (fun i ↦ (hv i).1)
    · ext x
      simp [hv]
  inter_ouvert := by
    rintro u v ⟨U, ⟨Uouv, hU⟩⟩ ⟨V, ⟨Vouv, hV⟩⟩
    use U ∩ V
    constructor
    · exact inter_ouvert Uouv Vouv
    · rw [hU, hV]; simp

def est_ouvert_elementaire (s : Set (X × X)) :=
  ∃ U1 U2 : Set X, (s = (U1 × U2)) ∧ (est_ouvert U1) ∧ (est_ouvert U2)

--instance top_prod {ι : Type}{u : ι → Set (X × X)} : EspTop (X × X) where
--  est_ouvert := fun w ↦ (w = ⋂ i, u i) ∧ (∀ i, est_ouvert_elementaire (u i))
--  univ_ouvert :=
