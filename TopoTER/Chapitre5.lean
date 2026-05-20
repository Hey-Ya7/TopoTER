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

variable {X : Type*}

open Metrique

--lemma sep_iff_diag_ferme :
--letI Δ : Set X := {x ∈ X | (x,x)}
--EspSepareT2 X ↔ est_ferme Δ

lemma diam_crois [EspaceMetrique X] {A : Partie X} {B : Partie X} :
diam_bornee B → A ⊆ B → diam A ≤ diam B := by
  intro bornB A_B
  unfold diam_bornee at bornB
  by_cases hA : A = ∅
  · rw [hA, diam_empty]
    rcases diam_nneg B with h | h
    · exact h
    · linarith
  · unfold diam at bornB
    dsimp at bornB
    split_ifs at bornB with h
    · unfold diam
      rw [if_pos h]
      dsimp
      split_ifs with h'
      · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hA
        apply csSup_le
        · use 0
          repeat use x; constructor; exact hx
          exact self_dist x
        · rintro d ⟨x, hx, y, hy, hxy⟩
          apply le_csSup h
          simp only [mem_setOf_eq]
          use x
          exact ⟨A_B hx, by use y; exact ⟨A_B hy, hxy⟩⟩
      · linarith
    · linarith

theorem thm_beurre [EspaceMetrique X] (F : ℕ → Partie X) : complet X →
(∀ n : ℕ, F n ≠ ∅ ∧ fermee (F n) ∧ ∀ m : ℕ, m ≥ n → (F m) ⊆ (F n)) →
converges_to (fun n ↦ diam (F n)) 0 -> ∃ x : X, ⋂ n : ℕ, F n = {x} := by
  intro compl hFn lim
  have h : ∀ n : ℕ, ∃ x : X, x ∈ F n := fun n ↦ Set.nonempty_iff_ne_empty.mpr (hFn n).1
  choose x hx using h
  have x_cau : cauchy x := by
    intro e e_pos
    let ε := min e 0.5
    have ε_pos : ε > 0 := lt_min e_pos (by norm_num)
    have ε_1 : ε < 1 := lt_of_le_of_lt (min_le_right e 0.5) (by linarith)
    have ε_e : ε ≤ e := min_le_left e 0.5
    rcases lim ε ε_pos with ⟨N, hN⟩
    use N
    intro n hn m hm
    let M : ℕ := min n m
    have hM : M ≥ N := Nat.le_min_of_le_of_le hn hm
    specialize hN M hM
    simp only at hN
    have dfm : diam (F M) ≠ -1 := by
      by_contra heq
      rw [heq] at hN
      have h_d1 : EspaceMetrique.d (-1 : ℝ) 0 = 1 := by
        change |(-1 : ℝ) - 0| = 1
        norm_num
      rw [h_d1] at hN
      linarith
    trans (diam (F M))
    · have Fn_FM : F n ⊆ F M := ((hFn M).2).2 _ (Nat.min_le_left n m)
      have Fm_FM : F m ⊆ F M := ((hFn M).2).2 _ (Nat.min_le_right n m)
      have hn : x n ∈ F M := Set.mem_preimage.mp (Fn_FM (hx n))
      have hm : x m ∈ F M := Set.mem_preimage.mp (Fm_FM (hx m))
      unfold diam at dfm
      dsimp at dfm
      split_ifs at dfm with hbdd
      · unfold diam
        rw [if_pos hbdd]
        apply le_csSup hbdd
        simp only [Set.mem_setOf_eq]
        use (x n)
        constructor
        · exact hn
        · use (x m)
      · contradiction
    · trans ε
      · change |diam (F M) - 0| ≤ ε at hN
        simp at hN
        rcases (diam_nneg (F M)) with h | h
        · linarith [abs_le.mp hN]
        · contradiction
      · exact ε_e
  specialize compl x x_cau
  rcases compl with ⟨l, hl⟩
  have hF : ∀ n : ℕ, ∀ m : ℕ, m ≥ n → x m ∈ F n := by
    intro n m hm
    exact (hFn n).2.2 m hm (hx m)
  have lfn : l ∈ ⋂ n : ℕ, F n := sorry
  have mborn : ∃ m : ℕ, ∀ n : ℕ, n ≥ m → diam_bornee (F n) := by
    rcases lim 0.5 (by linarith) with ⟨N, hN⟩
    dsimp at hN
    use N
    intro n hn
    unfold diam_bornee
    specialize hN n hn
    change |(diam (F n)) - 0| ≤ 0.5 at hN
    linarith [abs_le.mp hN]
  rcases mborn with ⟨N, hN⟩
  have hdiam : ∀ m : ℕ, m ≥ N → diam (⋂ n : ℕ, F n) ≤ diam (F m) := by
    intro m hm
    apply diam_crois
    · exact hN m hm
    · exact iInter_subset_of_subset m fun ⦃a⦄ a_1 ↦ a_1
  have diam_0 : ∀ ε > 0, diam (⋂ n : ℕ, F n) ≤ ε := by
    intro ε ε_pos
    rcases lim ε ε_pos with ⟨M, hM⟩
    change ∀ n ≥ M, |(diam (F n)) - 0| ≤ ε at hM
    specialize hdiam (max M N) (by simp)
    specialize hM (max M N) (by simp)
    trans diam (F (max M N))
    · exact hdiam
    · linarith [abs_le.mp hM]
  have diam_ge0 : diam (⋂ n : ℕ, F n) ≥ 0 := by
    rcases diam_nneg (⋂ n : ℕ, F n) with h | h
    · exact h
    · sorry
  have diam_0 : diam (⋂ n : ℕ, F n) = 0 := by
    by_contra! h
    sorry
  sorry

lemma h_split : Set.Icc 1 (n + 1) = insert (n + 1) (Set.Icc 1 n) := by
  ext x
  simp only [mem_Icc, mem_insert_iff]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases! h : 1 ≤ x ∧ x ≤ n
    · right
      exact h
    · left
      have h := h h1
      linarith
  intro h
  rcases h with h | h
  repeat constructor; repeat linarith

theorem thm_baire [EspaceMetrique X] : complet X → baire X := by
  intro X_compl U hU
  rw [dense_iff_inter_ouvert_nonempty]
  intro V V_ouv V_ne
  let W : ℕ → Partie X := fun n ↦ V ∩ (⋂ k ∈ Set.Icc 1 n, U k)
  have W_ouv : ∀ n : ℕ, est_ouvert (W n) := by
    intro n
    unfold W
    apply inter_ouvert V_ouv
    apply inter_fini_ouvert
    intro k _
    exact (hU k).2
  have W_ne : ∀ n : ℕ, (W n).Nonempty := by
    unfold W
    intro n
    induction n with
    | zero =>
      simp
      exact V_ne
    | succ n hr =>
      rw [h_split, biInter_insert]
      rw [Set.inter_comm (U (n+1)), ← Set.inter_assoc]
      change ((W n) ∩ U (n + 1)).Nonempty
      rcases hU (n + 1) with ⟨U_dens, U_ouv⟩
      rw [dense_iff_inter_ouvert_nonempty] at U_dens
      exact U_dens (W n) (W_ouv n) hr

  have hyp : ∀ n : ℕ, ∃ c : X, ∃ r > 0, boule_fermee c r ⊆ W n := by
    intro n
    specialize W_ouv n
    rw [ouvert_ssi_vois] at W_ouv
    rcases W_ne n with ⟨x, hx⟩
    rcases W_ouv x hx with ⟨u, hu⟩
    use x
    use (diam u)/4
    sorry
  sorry
