import TopoTER.Chapitre4

open TER Set EspTop

variable {X : Type*} [EspTop X]
variable {Y : Type*} [EspSepareT2 Y]

def prop_baire {X : Type*} [EspTop X] (u : ℕ → Set X) := (∀ (n : ℕ),
  dense X (u n) ∧ est_ouvert (u n)) → dense X (⋂ n : ℕ, u n)

def baire (X : Type*) [EspTop X] : Prop := ∀ (u : ℕ → Set X), prop_baire u

lemma baire_ouvert (h : baire X) (v : Set X) : est_ouvert v → baire v := by
  rintro hv u hu
  let U : ℕ -> Set X := fun n ↦ (u n) ∪ ((adh v)ᶜ)

  have Uouv : ∀ (n : ℕ), est_ouvert (U n) := by
    intro n
    unfold U
    --rw [hU n]
    apply union_est_ouvert
    · have h : est_ouvert (u n) := (hu n).2
      rcases h with ⟨w, hw, h'⟩
      simp [h', inter_ouvert hv hw]
    · rw [est_ouvert_iff_compl_est_ferme, compl_compl]
      exact adh_ferme v

  have Udens : ∀ (n : ℕ), dense X (U n) := by
    intro n
    rw [dense_iff_inter_ouvert_nonempty]
    intro W W_ouv W_ne
    rcases W_ne with ⟨x, hx⟩
    have W_vois : est_vois x W := by -- ⟨W, hx, W_ouv, by simp⟩
      use W
      exact ⟨hx, W_ouv, by simp⟩
    let W_sub : Set v := Subtype.val ⁻¹' W
    have Ws_ouv : est_ouvert W_sub := by use W
    rcases (hu n) with ⟨u_dens, u_ouv⟩
    rw [dense_iff_inter_ouvert_nonempty] at u_dens

    by_cases x_v : x ∈ v
    · have Ws_ne : W_sub.Nonempty := by
        unfold W_sub
        use ⟨x, x_v⟩
        simp only [mem_preimage]
        rcases W_vois with ⟨U, ⟨x_U, _, U_W⟩⟩
        exact U_W x_U
      specialize u_dens W_sub Ws_ouv Ws_ne
      rcases u_dens with ⟨y, ⟨y_Ws, y_u⟩⟩
      use y
      constructor
      · exact y_Ws
      · unfold U
        left
        simp
        exact y_u

    · by_cases x_adh : x ∈ (adh v)
      · have Ws_ne : W_sub.Nonempty := by
          specialize x_adh W W_vois
          rcases x_adh with ⟨y, hy⟩
          use ⟨y, hy.2⟩
          unfold W_sub
          simp only [mem_preimage]
          exact hy.1
        unfold adh at x_adh
        simp only [mem_setOf_eq] at x_adh
        specialize x_adh W W_vois
        specialize u_dens W_sub Ws_ouv Ws_ne
        rcases u_dens with ⟨y, ⟨y_Ws, y_u⟩⟩
        use y
        constructor
        · exact y_Ws
        · unfold U
          left
          simp
          exact y_u
      · use x
        constructor
        · exact hx
        · right
          exact x_adh
  unfold baire prop_baire at h
  have h' : dense X (⋂ n, U n) := by
    apply h
    intro n
    exact ⟨Udens n, Uouv n⟩
  unfold dense adh at h'
  unfold dense adh
  ext x
  simp only [mem_setOf_eq, mem_univ, iff_true]
  intro W W_vois
  rw [Set.eq_univ_iff_forall] at h'
  specialize h' x
  rw [mem_setOf_eq] at h'
  specialize h' W
  have Wsub_vois : est_vois (↑x) (Subtype.val '' W) := by
    rcases W_vois with ⟨w, ⟨x_w, w_ouv, w_W⟩⟩
    use w
    constructor
    · simp
      exact x_w
    · rcases w_ouv with ⟨A, hA⟩
      rw [hA.2]
      simp only [Subtype.image_preimage_coe]
      exact inter_ouvert hv hA.1
    · simp
      exact w_W
  specialize h' Wsub_vois
  rcases h' with ⟨y, ⟨y_W, y_U⟩⟩
  rcases y_W with ⟨z, z_W, rfl⟩
  use z
  constructor
  · exact z_W
  · rw [Set.mem_iInter]
    intro n
    have z_Un : ↑z ∈ U n := by
      rw [Set.mem_iInter] at y_U
      exact y_U n
    unfold U at z_Un
    rcases z_Un with z_un | z_nadh
    · simp? at z_un
      exact z_un
    · rw [mem_compl_iff] at z_nadh
      have z_adh : ↑z ∈ adh v := by
        apply contenu_adh
        simp
      by_contra _
      exact z_nadh z_adh

--def topo_engendree (S : Set (Set X)) : EspTop X where
--  est_ouvert := _
--  univ_ouvert := _
--  empty_ouvert := _
--  union_ouvert := _
--  inter_ouvert := _
