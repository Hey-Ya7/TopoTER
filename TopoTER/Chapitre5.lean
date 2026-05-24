import TopoTER.Chapitre4
set_option linter.style.emptyLine false

open TER Set EspTop

variable {X Y : Type} [EspTop X] [EspTop Y] [EspSepareT2 Y]

def prop_baire {X : Type} [EspTop X] (u : ℕ → Set X) := (∀ (n : ℕ),
  dense X (u n) ∧ est_ouvert (u n)) → dense X (⋂ n : ℕ, u n)

def baire (X : Type) [EspTop X] : Prop := ∀ (u : ℕ → Set X), prop_baire u

lemma baire_ouvert (hb : baire X) (v : Set X) : est_ouvert v → baire (Induite v)
  := by
  rintro hv u hu
  let U : ℕ -> Set X := fun n ↦ (u n) ∪ ((adh v)ᶜ)

  have Uouv : ∀ (n : ℕ), est_ouvert (U n) := by
    intro n; unfold U
    apply union_est_ouvert
    · have h : est_ouvert (u n) := (hu n).2
      rcases h with ⟨w, hw, h'⟩
      simp [h', inter_ouvert hv hw]
    · rw [est_ouvert_iff_compl_est_ferme, compl_compl]
      exact adh_ferme

  have Udens : ∀ (n : ℕ), dense X (U n) := by
    intro n
    rw [dense_iff_inter_ouvert_nonempty]
    intro W W_ouv W_ne
    rcases W_ne with ⟨x, hx⟩
    have W_vois : est_vois x W := by --⟨W, ⟨hx, W_ouv, by simp⟩⟩
      use W
      exact ⟨hx, W_ouv, by simp⟩
    let W_sub : Set (Induite v) := Subtype.val ⁻¹' W
    have Ws_ouv : est_ouvert W_sub := by use W
    rcases (hu n) with ⟨u_dens, u_ouv⟩
    rw [dense_iff_inter_ouvert_nonempty] at u_dens

    by_cases x_adh : x ∈ adh v
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
        simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
          Subtype.coe_prop, exists_const]
        exact y_u
    · use x
      constructor
      · exact hx
      · right
        exact x_adh

  unfold baire prop_baire at hb
  have h' : dense X (⋂ n, U n) := by
    apply hb
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
    · simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
      Subtype.coe_prop, exists_const]
      exact x_w
    · rcases w_ouv with ⟨A, hA⟩
      rw [hA.2]
      simp only [Subtype.image_preimage_coe]
      exact inter_ouvert hv hA.1
    · simp only [image_subset_iff, Subtype.val_injective, preimage_image_eq]
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
    · simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
      Subtype.coe_prop, exists_const] at z_un
      exact z_un
    · rw [mem_compl_iff] at z_nadh
      have z_adh : ↑z ∈ adh v := by
        apply contenu_adh
        simp
      by_contra _
      exact z_nadh z_adh

variable {X : Type}

open Metrique

lemma cauchy_unif_continu_cauchy [EspaceMetrique X] [EspaceMetrique Y] (f : X → Y)
(hcont : unif_continu f) (u : ℕ → X) (h : cauchy u): cauchy (f ∘ u) := by
  unfold cauchy at *
  unfold unif_continu at hcont
  intro ε ε_pos
  specialize hcont ε ε_pos
  rcases hcont with ⟨δ, ⟨hδ_pos, hconvδ⟩⟩
  specialize h δ hδ_pos
  rcases h with ⟨N, hnN⟩
  use N
  intro m hm n hn
  specialize hnN m hm n hn
  specialize hconvδ (u m) (u n) hnN
  exact hconvδ

lemma diag_inter_empty {W : Type*} (U : Set W) (V : Set W) :
  let Δ : Set (W×W) := {p : W×W | p.1 = p.2}
  U ∩ V = ∅ ↔ (U ×ˢ V) ⊆ Δᶜ := by
    constructor
    · intro huv (x, y) hxy hf
      dsimp at hf
      simp_all
      rw[← mem_inter_iff] at hxy
      simp_all
    · contrapose!
      intro hne h
      rcases hne with ⟨p, hp⟩
      have hpint : (p,p) ∈ U ×ˢ V := mem_prod.mpr hp
      exact false_of_ne fun a ↦ h hpint a

lemma voisinage_produit_fini {X : Type*} [EspTop X] (H : Set (Fin 2 → X)) (hH : est_ouvert H) (f : Fin 2 → X) (hf : f ∈ H) :
  ∃ (U V : Set X), est_ouvert U ∧ est_ouvert V ∧ f 0 ∈ U ∧ f 1 ∈ V ∧ {g | g 0 ∈ U} ∩ {g | g 1 ∈ V} ⊆ H := by
    change ouv_top_engendree _ H at hH




lemma sep_iff_diag_ferme {X : Type*} [EspTop X] :
  letI E : EspTop (Fin 2 → X) := top_prod_fini (fun i ↦ X)
  let Δ : Partie (Fin 2 → X) := {f | f 0 = f 1}
  EspSepareT2 X ↔ est_ferme Δ := by
    have h : {f : (Fin 2 → X) | f 0 = (f 1)}ᶜ = {f | f 0 ≠ f 1} := by
        ext f
        simp only [mem_compl_iff, mem_setOf_eq]
    constructor
    · intro hSep
      rw[est_ferme]
      rw[h]
      rw[ouvert_ssi_vois]
      intro f hf
      rw[mem_setOf_eq] at hf
      have h0 : ∃ (U V : Set X),
      (est_ouvert U) ∧ (est_ouvert V) ∧ ((f 0) ∈ U) ∧ ((f 1) ∈ V) ∧ (U ∩ V = ∅) := by
        exact EspSepareT2.est_separe (f 0) (f 1) hf
      rcases h0 with ⟨U, V, U_ouv, V_ouv, f0U, f1V, U_V⟩
      use {f | f 0 ∈ U} ∩ {f | f 1 ∈ V}
      constructor
      · constructor
        · exact mem_setOf.mpr f0U
        · exact mem_setOf.mpr f1V
      · apply inter_ouvert
        · apply ouvert_pref_projections
          exact U_ouv
        · apply ouvert_pref_projections
          exact V_ouv
      · have h_prod : U ×ˢ V ⊆ {p : X × X | p.1 = p.2}ᶜ := by exact (diag_inter_empty U V).mp U_V
        intro g hg
        rcases hg with ⟨g0_U, g1_V⟩
        have h_couple : (g 0, g 1) ∈ U ×ˢ V := ⟨g0_U, g1_V⟩
        have h_not_diag := h_prod h_couple
        exact h_not_diag
    · intro hFerme
      refine { est_separe := by
                              intro x y hxy;
                              rw[est_ferme, h, ouvert_ssi_vois] at hFerme
                              let proj : Fin 2 → X := fun | 0 => x | 1 => y
                              have proj_in_ferme : proj ∈ {f | f 0 ≠ f 1} := by
                                exact mem_setOf.mpr hxy
                              specialize hFerme proj proj_in_ferme
                              rcases hFerme with ⟨H, ⟨hprojH, houvH, hHin⟩⟩

                              --rw[est_ouvert] at houvH








             }


intro g hg
        rw[←h]
        intro hfalg
        have ghg : (g 0 ∈ U) ∧ (g 1 ∈ V) := by
          simp only [mem_inter_iff, mem_setOf_eq] at hg
          exact hg
        have g0g1 : g 0 = g 1 := by
          exact ((fun a ↦ hfalg) ∘ fun a ↦ X) X
        have g0U : g 0 ∈ U ∩ V:= by
          constructor
          · exact ghg.1
          · rw[g0g1]
            exact ghg.2
        simp_all


lemma diam_gt_0 [EspaceMetrique X] {A : Partie X} :
(A = ∅ ∨ ∃ x : X, A = {x}) ↔ diam A = 0 := by
  constructor
  · intro h
    rcases h with h | ⟨x, hx⟩
    · subst A
      exact diam_empty
    · unfold diam
      sorry
  · sorry
lemma diam_born_sub [EspaceMetrique X] {A : Partie X} {B : Partie X} :
diam_bornee B → A ⊆ B → diam_bornee A := by
  intro bornB A_B
  rw [bornee_iff_bdd]
  rw [bornee_iff_bdd] at bornB
  unfold dist_bornee
  unfold dist_bornee at bornB
  rcases bornB with ⟨M, hM⟩
  exact ⟨M,
  fun x hx y hy ↦ hM x (Set.mem_of_mem_of_subset hx A_B) y (Set.mem_of_mem_of_subset hy A_B)⟩

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

lemma crois_equ [EspaceMetrique X] {F : ℕ → Partie X} :
(∀ n m : ℕ, m ≥ n → (F m) ⊆ (F n)) ↔ (∀ n : ℕ, (F (n + 1)) ⊆ (F n)) := by
  constructor
  · intro h n
    apply h
    linarith
  · intro h sylvie m hm
    induction m, hm using Nat.le_induction with
    | base =>
      rfl
    | succ laetitia hk hr =>
      trans F laetitia
      · exact h laetitia
      · exact hr

lemma diam_0_singl_or_empty [EspaceMetrique X] {A : Partie X} :
A.Nonempty → diam A = 0 → ∃ x : X, A = {x} := by
  rintro ⟨x, hx⟩ diam_0
  use x
  ext y
  constructor
  · intro hy
    unfold diam at diam_0
    dsimp at diam_0
    split_ifs at diam_0 with h
    · let S := {d | ∃ a ∈ A, ∃ b ∈ A, EspaceMetrique.d a b = d}
      have d_diam : EspaceMetrique.d x y ≤ sSup S := le_csSup h ⟨x, hx, y, hy, rfl⟩
      rw [diam_0] at d_diam
      have d_0 : EspaceMetrique.d x y = 0 := le_antisymm d_diam (EspaceMetrique.is_dist.nneg x y)
      rw [(EspaceMetrique.is_dist.sep x y).mp d_0]
      rfl
    · linarith
  · intro hy
    rw [hy]
    exact hx

lemma ouv_contient_b_centre [EspaceMetrique X] {U : Partie X} {c : X} :
est_ouvert U → c ∈ U → ∃ r > 0, Bₒ c r ⊆ U := by
  intro U_ouv hc
  rcases U_ouv c hc with ⟨r, r_pos, h⟩
  use r

lemma ouv_contient_b [EspaceMetrique X] {U : Partie X} :
est_ouvert U → U.Nonempty → ∃ c : X, ∃ r > 0, Bₒ c r ⊆ U :=
  fun U_ouv ⟨c, hc⟩ ↦ ⟨c, ouv_contient_b_centre U_ouv hc⟩

lemma ouv_contient_bf_centre [EspaceMetrique X] {U : Partie X} :
est_ouvert U → c ∈ U → ∃ r > 0, Bf c r ⊆ U := by
  intro U_ouv hc
  rcases U_ouv c hc with ⟨r, r_pos, h⟩
  exact ⟨r/2, half_pos r_pos, fun x hx ↦ h (by simp at *; linarith)⟩

lemma ouv_contient_bf [EspaceMetrique X] {U : Partie X} :
est_ouvert U → U.Nonempty → ∃ c : X, ∃ r > 0, Bf c r ⊆ U :=
  fun U_ouv ⟨c, hc⟩ ↦ ⟨c, ouv_contient_bf_centre U_ouv hc⟩

lemma conv_equ [EspaceMetrique X] {u : ℕ → X} {l : X} :
converge_vers u l ↔ converges_to u l := by
  unfold converge_vers converges_to
  constructor
  · intro conv ε ε_pos
    have B_vois : est_vois l (Bₒ l ε) :=
      ⟨Bₒ l ε, centre_in_boule l ε_pos, ouv_of_boule_ouv l ε, by rfl⟩
    rcases conv (Bₒ l ε) B_vois with ⟨N, hN⟩
    use N
    intro n hn
    specialize hN n hn
    simp at hN
    linarith [hN]
  · rintro conv V ⟨v, l_v, v_ouv, v_V⟩
    rcases ouv_contient_bf_centre v_ouv l_v with ⟨r, r_pos, B_v⟩
    rcases conv r r_pos with ⟨N, hN⟩
    use N
    intro n hn
    specialize hN n hn
    apply B_v.trans
    · exact v_V
    · simp only [boule_fermee.eq_1, mem_setOf_eq, hN]

lemma conv_ge_N_equ [EspTop X] {u : ℕ → X} {v : ℕ → X} {l : X} {N : ℕ} :
(∀ n ≥ N, u n = v n) → (converge_vers u l ↔ converge_vers v l) := by
  intro h
  unfold converge_vers
  constructor
  · intro conv_u V V_vois
    rcases conv_u V V_vois with ⟨M, hM⟩
    use max M N
    intro m hm
    rw [←h m (le_of_max_le_right hm)]
    exact hM m (le_of_max_le_left hm)
  · intro conv_u V V_vois
    rcases conv_u V V_vois with ⟨M, hM⟩
    use max M N
    intro m hm
    rw [h m (le_of_max_le_right hm)]
    exact hM m (le_of_max_le_left hm)

theorem pre_thm_baire [EspaceMetrique X] {F : ℕ → Partie X} : complet X →
(∀ n : ℕ, F n ≠ ∅) → (∀ n : ℕ, fermee (F n)) → (∀ n m : ℕ, m ≥ n → (F m) ⊆ (F n)) →
converges_to (fun n ↦ diam (F n)) 0 -> ∃ x : X, ⋂ n : ℕ, F n = {x} := by
  intro compl F_ne F_fer F_decrois lim
  have h : ∀ n : ℕ, ∃ x : X, x ∈ F n := fun n ↦ Set.nonempty_iff_ne_empty.mpr (F_ne n)
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
    · have Fn_FM : F n ⊆ F M := (F_decrois M) _ (Nat.min_le_left n m)
      have Fm_FM : F m ⊆ F M := (F_decrois M) _ (Nat.min_le_right n m)
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

  rcases compl x x_cau with ⟨l, hl⟩

  have hF : ∀ n : ℕ, ∀ m : ℕ, m ≥ n → x m ∈ F n := by
    intro n m hm
    exact (F_decrois n) m hm (hx m)

  have inter_fer : fermee (⋂ n : ℕ, F n) := by
    change est_ferme (⋂ n, F n)
    exact inter_est_ferme F_fer

  have lfn : l ∈ ⋂ n : ℕ, F n := by
    rw [mem_iInter]
    intro n
    have ⟨N, hN⟩ : ∃ m : ℕ, m ≥ n := exists_nat_ge n
    have h : (x N) ∈ (F n) := mem_preimage.mp (hF n N hN)
    change ∀ (n : ℕ), est_ferme (F n) at F_fer
    specialize F_fer n
    rw [ferme_iff_adh] at F_fer
    rw [←F_fer, in_adh_suite]
    let y : ℕ → X := m ↦ if m < n then x n else x m
    use y
    constructor
    · intro m
      by_cases m_n : m < n
      · simp only [m_n, ↓reduceIte, y]
        exact hF n n (by rfl)
      · simp only [m_n, ↓reduceIte, y]
        push_neg at m_n
        exact hF n m m_n
    · have x_eq_y : ∀ m ≥ n, x m = y m := by
        intro m hm
        simp [y, hm]
      rw [←conv_ge_N_equ x_eq_y, conv_equ]
      exact hl
  have mborn : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → diam_bornee (F n) := by
    rcases lim 0.5 (by linarith) with ⟨N, hN⟩
    dsimp at hN
    use N
    intro n hn
    unfold diam_bornee
    specialize hN n hn
    change |(diam (F n)) - 0| ≤ 0.5 at hN
    linarith [abs_le.mp hN]

  rcases mborn with ⟨N, hN⟩

  have inter_in_F : ∀ m, ⋂ n, F n ⊆ F m := m ↦ iInter_subset_of_subset m (by rfl)

  have born : diam_bornee (⋂ n : ℕ, F n) := diam_born_sub (hN N (by rfl)) (inter_in_F N)

  have diam_pos : diam (⋂ n : ℕ, F n) ≥ 0 := by
    rcases diam_nneg (⋂ n : ℕ, F n) with h | h
    · exact h
    · unfold diam_bornee at born
      linarith

  have hdiam : ∀ m : ℕ, m ≥ N → diam (⋂ n : ℕ, F n) ≤ diam (F m) :=
    fun m hm ↦ diam_crois (hN m hm) (inter_in_F m)

  have diam_0 : ∀ ε > 0, diam (⋂ n : ℕ, F n) ≤ ε := by
    intro ε ε_pos
    rcases lim ε ε_pos with ⟨M, hM⟩
    change ∀ n ≥ M, |(diam (F n)) - 0| ≤ ε at hM
    specialize hdiam (max M N) (by simp)
    specialize hM (max M N) (by simp)
    trans diam (F (max M N))
    · exact hdiam
    · linarith [abs_le.mp hM]

  have h_le : diam (⋂ n, F n) ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    rw[zero_add]
    exact diam_0 ε hε

  have diam_0 : diam (⋂ n : ℕ, F n) = 0 := le_antisymm h_le diam_pos

  exact diam_0_singl_or_empty ⟨l, lfn⟩ diam_0

lemma h_split {n : ℕ} : Set.Icc 0 (n + 1) = insert (n + 1) (Set.Icc 0 n) := by
  ext x
  simp only [mem_Icc, mem_insert_iff]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases! h : 0 ≤ x ∧ x ≤ n
    · right
      exact h
    · left
      have h := h h1
      linarith
  intro h
  rcases h with h | h
  repeat constructor; repeat linarith

lemma lemme1 {U : ℕ → Partie X} : ⋂ n, U n = ⋂ n, ⋂ k ∈ Icc 0 n, U k := by
  ext x
  simp only [mem_Icc, zero_le, true_and, mem_iInter]
  exact ⟨fun h _ m _ ↦ h m, fun h n ↦ h n n (by simp)⟩

lemma lemme2 {V : Partie X} {U : ℕ → Partie X} :
V ∩ ⋂ n, ⋂ k ∈ Icc 0 n, U k = ⋂ n, V ∩ ⋂ k ∈ Icc 0 n, U k := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  exact ⟨fun h n ↦ ⟨h.1, h.2 n⟩, h ↦ ⟨(h 0).1, fun n m hm ↦ (h n).2 m hm⟩⟩

theorem thm_baire [EspaceMetrique X] : complet X → baire X := by
  intro X_compl U hU
  rw [dense_iff_inter_ouvert_nonempty]
  intro V V_ouv V_ne
  let W : ℕ → Partie X := fun n ↦ V ∩ (⋂ k ∈ Set.Icc 0 n, U k)

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
      simp only [Icc_self, mem_singleton_iff, iInter_iInter_eq_left]
      rcases hU 0 with ⟨dens, _⟩
      rw [dense_iff_inter_ouvert_nonempty] at dens
      exact dens V V_ouv V_ne
    | succ n hr =>
      rw [h_split, biInter_insert]
      rw [Set.inter_comm (U (n+1)), ← Set.inter_assoc]
      change ((W n) ∩ U (n + 1)).Nonempty
      rcases hU (n + 1) with ⟨U_dens, U_ouv⟩
      rw [dense_iff_inter_ouvert_nonempty] at U_dens
      exact U_dens (W n) (W_ouv n) hr

  let B_ok (n : ℕ) (c : X) (r : ℝ) : Prop := r > 0 ∧ r ≤ 1 / (2*(↑n + 1)) ∧ Bf c r ⊆ W n

  have H : ∃ c : ℕ → X, ∃ r : ℕ → ℝ, (∀ n, B_ok n (c n) (r n)) ∧
                         (∀ n, Bf (c (n+1)) (r (n+1)) ⊆ Bf (c n) (r n)) := by

    rcases ouv_contient_bf (W_ouv 0) (W_ne 0) with ⟨c0, r0, r0_pos, h0⟩

    have B0_ok : B_ok 0 c0 (min r0 (1/2)) := by
      unfold B_ok
      constructor
      · simp [r0_pos]
      · constructor
        · simp
        · apply subset_trans _ h0
          exact boule_f_in_boule_f_ge c0 (by simp [r0_pos]) r0_pos (min_le_left r0 (1 / 2))

    have Bn_ok : ∀ n : ℕ, ∀ p : X × ℝ, B_ok n p.1 p.2 →
            ∃ q : X × ℝ, B_ok (n + 1) q.1 q.2 ∧ Bf q.1 q.2 ⊆ Bf p.1 p.2:= by
      rintro n p ⟨r_pos, r_le, h⟩
      have ouv : est_ouvert (Bₒ p.1 p.2 ∩ U (n + 1)) :=
        inter_ouvert (ouv_of_boule_ouv p.1 p.2) (hU (n + 1)).2
      have ne : (Bₒ p.1 p.2 ∩ U (n + 1)).Nonempty := by
        rcases hU (n + 1) with ⟨U_dens, U_ouv⟩
        rw [dense_iff_inter_ouvert_nonempty] at U_dens
        apply U_dens (Bₒ p.1 p.2) (ouv_of_boule_ouv p.1 p.2)
        use p.1
        simp only [boule_ouverte, mem_setOf_eq]
        have h : EspaceMetrique.d p.1 p.1 = 0 := by rw [EspaceMetrique.is_dist.sep p.1 p.1]
        rw [h]
        exact r_pos
      rcases ouv_contient_bf ouv ne with ⟨c_next, R, R_pos, hR⟩
      let r_next := min R (1 / (2*(n + 2)))
      use (c_next, r_next)
      have bf_in_bf := boule_f_in_boule_f_ge c_next (by positivity) R_pos
                        (min_le_left R (1 / (2*(↑n + 2))))
      have hyp : Bf c_next r_next ⊆ Bₒ p.1 p.2 ∩ U (n + 1) := by
        intro x hx
        apply bf_in_bf at hx
        apply hR at hx
        exact hx
      constructor
      · constructor
        · unfold r_next
          simp [R_pos]
          linarith
        · constructor
          · unfold r_next
            push_cast
            ring_nf
            exact min_le_right _ _
          · apply hyp.trans
            unfold W
            rw [h_split, Set.biInter_insert, inter_comm (U (n + 1)), ←inter_assoc]
            apply inter_subset_inter
            · change Bₒ p.1 p.2 ⊆ W n
              apply subset_trans (boule_in_boule_f p.1 r_pos) h
            · rfl
      · exact subset_trans hyp (subset_trans inter_subset_left (boule_in_boule_f p.1 r_pos))

    choose! f hf using Bn_ok
    let B : ℕ → X × ℝ := fun n ↦ Nat.recOn n (c0, (min r0 (1/2))) f
    let c n := (B n).1
    let r n := (B n).2
    use c, r

    have B_ok_n : ∀ n, B_ok n (c n) (r n) := by
      intro n
      induction n with
      | zero => exact B0_ok
      | succ n hr => exact (hf n (B n) hr).1

    constructor
    · exact B_ok_n
    · intro n
      exact (hf n (B n) (B_ok_n n)).2

  choose c r Bn_ok bf_in_bf using H
  let B : ℕ → Partie X := n ↦ Bf (c n) (r n)
  change ∀ (n : ℕ), B (n + 1) ⊆ B n at bf_in_bf

  have c_B : ∀ n : ℕ, c n ∈ B n := by
    intro n
    have h'' : EspaceMetrique.d (c n) (c n) = 0 := by
      rw [EspaceMetrique.is_dist.sep (c n) (c n)]
    simp [B, h'']
    linarith [(Bn_ok n).1]

  have B_diam_pos : ∀ n : ℕ, diam (B n) ≥ 0 := by
    intro n
    rcases diam_nneg (B n) with h | h
    · exact h
    · have B_in_boule : in_boule (B n) := by
        use (c n), 2*(r n)
        simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left, boule_ouverte]
        exact ⟨(Bn_ok n).1, fun _ hx ↦ lt_of_le_of_lt hx (lt_two_mul_self ((Bn_ok n).1))⟩
      rw [←bdd_iff_in_boule, ←bornee_iff_bdd] at B_in_boule
      unfold diam_bornee at B_in_boule
      have nh : diam (B n) ≠ -1 := ne_of_gt B_in_boule.2
      contradiction

  have B_diam_le_inv : ∀ n : ℕ, diam (B n) ≤ 1/(n + 1) := by
    intro n
    unfold diam
    dsimp
    split_ifs with h'
    · apply csSup_le
      · use 0, c n
        have h'' : EspaceMetrique.d (c n) (c n) = 0 := by
          rw [EspaceMetrique.is_dist.sep (c n) (c n)]
        exact ⟨c_B n, c n, c_B n, h''⟩
      · simp only [mem_setOf_eq, one_div, forall_exists_index, and_imp]
        intro d x hx y hy h
        have h_dist : ∀ z : X, z ∈ B n → EspaceMetrique.d z (c n) ≤ (min (r n) (1 / (2*(↑n + 1))))
        := by
          intro z hz
          simp only [boule_fermee.eq_1, mem_setOf_eq, B] at hz
          simp only [one_div, mul_inv_rev, le_inf_iff]
          constructor
          · exact hz
          · specialize Bn_ok n
            rcases Bn_ok with ⟨h1, h2, h3⟩
            apply hz.trans
            have h_calc : 1 / (2 * ((n : ℝ) + 1)) = ((n : ℝ) + 1)⁻¹ * 2⁻¹ := by field_simp
            rw [←h_calc]
            exact h2
        rw [←h]
        calc EspaceMetrique.d x y
          ≤ EspaceMetrique.d x (c n) + EspaceMetrique.d (c n) y :=
            EspaceMetrique.is_dist.ineq x (c n) y
          _ ≤ (min (r n) (1 / (2*(↑n + 1)))) + (min (r n) (1 / (2*(↑n + 1)))) :=
            add_le_add (h_dist x hx) (by rw [EspaceMetrique.is_dist.symm]; exact (h_dist y hy))
          _ = 2 * (min (r n) (1 / (2*(↑n + 1)))) := by ring
          _ ≤ 2 * (1 / (2*(↑n + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
          _ ≤ (↑n + 1)⁻¹ := by field_simp; rfl
    · trans 0
      · linarith
      · apply one_div_nonneg.mpr ?_
        linarith

  have B_diam : converges_to (n ↦ (diam (B n))) 0 := by
    exact conv_of_le_inv (n ↦ diam (B n)) B_diam_pos B_diam_le_inv

  apply pre_thm_baire X_compl at B_diam

  · rcases B_diam with ⟨x, hx⟩
    have h : (⋂ n, B n).Nonempty := by
      use x
      rw [hx]
      rfl
    have B_W  : ⋂ n, B n ⊆ ⋂ n, V ∩ ⋂ k ∈ Icc 0 n, U k := Set.iInter_mono (n ↦ (Bn_ok n).2.2)
    rw [lemme1, lemme2]
    exact Nonempty.mono B_W h

  · intro n
    rw [← Set.nonempty_iff_ne_empty]
    exact ⟨c n, c_B n⟩

  · exact n ↦ fermee_of_boule_f (c n) (r n)

  · exact crois_equ.mpr (n ↦ bf_in_bf n)

--comm tournoi OMP : balatro maxxing
--mardi 26 mai a 15h avec un thm chacun (1/2 heure chacun)
--nettoyer le code qui a mettre des sorry
--rapport même si c'est pas mega complet, surtout il faut qu'il y ait ce qu'on presente mardi
