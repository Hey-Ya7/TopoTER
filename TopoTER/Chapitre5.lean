import TopoTER.Chapitre4

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
    let W_sub : Set (Induite v) := Subtype.val ⁻¹' W
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

variable {X : Type}

open Metrique

--lemma sep_iff_diag_ferme :
--letI Δ : Set X := {x ∈ X | (x,x)}
--EspSepareT2 X ↔ est_ferme Δ

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

theorem thm_beurre [EspaceMetrique X] {F : ℕ → Partie X} : complet X →
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
    · specialize hN N (by rfl)
      have tizi : (⋂ n, F n) ⊆ (F N) := by
        exact iInter_subset_of_subset N fun ⦃a⦄ a_1 ↦ a_1
      sorry

  have diam_0 : diam (⋂ n : ℕ, F n) = 0 := by
    by_contra! h
    have hyp := Std.lt_of_le_of_ne diam_ge0 (id (Ne.symm h))
    sorry

  sorry

lemma h_split {n : ℕ} : Set.Icc 1 (n + 1) = insert (n + 1) (Set.Icc 1 n) := by
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

noncomputable def diam2 [EspaceMetrique X] (A : Partie X) :=
  let S := {d(x, y) | (x ∈ A) (y ∈ A)}; sSup S

lemma ouv_metr [EspaceMetrique X] {U : Partie X} :
est_ouvert U ↔ ∀ x : X, x ∈ U → ∃ r > 0, boule_ouverte x r ⊆ U := sorry

lemma fer_of_boule_fer [EspaceMetrique X] (a : X) (r : ℝ) : fermee (Bf a r) := sorry

lemma ouv_contient_bf [EspaceMetrique X] {U : Partie X} :
est_ouvert U → U.Nonempty → ∃ c : X, ∃ r > 0, Bf c r ⊆ U := by
  intro U_ouv U_ne
  obtain ⟨c, hc⟩ := U_ne
  rw [ouv_metr] at U_ouv
  rcases U_ouv c hc with ⟨r, r_pos, h⟩
  use c, r/2
  exact ⟨half_pos r_pos, fun x hx ↦ h (by simp at *; linarith)⟩

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

  let B_ok (n : ℕ) (c : X) (r : ℝ) : Prop := r > 0 ∧ r ≤ 1 / (↑n + 2) ∧ Bf c r ⊆ W n

  have B_succ_ok : ∀ n : ℕ, ∃ c : X, ∃ r : ℝ, B_ok n c r := by
    intro n
    induction n with
    | zero =>
      unfold B_ok
      rcases ouv_contient_bf (W_ouv 0) (W_ne 0) with ⟨c, r, r_pos, h⟩
      use c, min r (1/2)
      constructor
      · simp [r_pos]
      · constructor
        · simp
        · intro x hx
          simp at *
          exact h hx.1
    | succ n hr =>
      rcases hr with ⟨c, r, r_pos, _, Bf_W⟩
      have ouv : est_ouvert (Bₒ c r ∩ U (n + 1)) :=
        inter_ouvert (ouv_of_boule_ouv c r) (hU (n + 1)).2
      have ne : (Bₒ c r ∩ U (n + 1)).Nonempty := by
        rcases hU (n + 1) with ⟨U_dens, U_ouv⟩
        rw [dense_iff_inter_ouvert_nonempty] at U_dens
        apply U_dens (Bₒ c r) (ouv_of_boule_ouv c r)
        use c
        simp only [boule_ouverte, mem_setOf_eq]
        have h : EspaceMetrique.d c c = 0 := by rw [EspaceMetrique.is_dist.sep c c]
        rw [h]
        exact r_pos
      rcases ouv_contient_bf ouv ne with ⟨c_next, R, R_pos, hR⟩
      let r_next := min R (1 / (n + 3))
      use c_next, r_next
      constructor
      · exact lt_min R_pos (by positivity)
      · constructor
        · unfold r_next
          push_cast
          ring_nf
          exact min_le_right _ _
        · have hyp : Bf c_next r_next ⊆ Bₒ c r ∩ U (n + 1) := by
            intro x hx
            have bf_in_bf := boule_f_in_boule_f_ge c_next (by positivity) R_pos (min_le_left R (1 / (↑n + 3)))
            apply bf_in_bf at hx
            apply hR at hx
            exact hx
          apply hyp.trans
          unfold W
          rw [h_split, Set.biInter_insert, inter_comm (U (n + 1)), ←inter_assoc]
          apply inter_subset_inter
          change Bₒ c r ⊆ W n
          apply subset_trans (boule_in_boule_f c r_pos) Bf_W
          rfl

  choose c r r_pos h_sub using B_succ_ok

  let B : ℕ → Partie X := n ↦ boule_fermee (c n) (min (r n) (1/(2*(n + 1))))

  have B_bf : ∀ n : ℕ, B n ⊆ boule_fermee (c n) (r n) := by
    intro _
    simp only [boule_fermee, one_div, mul_inv_rev, le_inf_iff, setOf_subset_setOf, and_imp, B]
    exact fun _ hx _ ↦ hx

  have B_W : ∀ n : ℕ, B n ⊆ W n := by
    intro n
    trans boule_fermee (c n) (r n)
    · exact B_bf n
    · exact (h_sub n).2

  have c_B : ∀ n : ℕ, c n ∈ B n := by
    intro n
    have h'' : EspaceMetrique.d (c n) (c n) = 0 := by
      rw [EspaceMetrique.is_dist.sep (c n) (c n)]
    simp only [boule_fermee, one_div, mul_inv_rev, le_inf_iff, mem_setOf_eq, B]
    rw [h'']
    constructor
    · exact Std.le_of_lt (r_pos n)
    · apply mul_nonneg
      · apply inv_nonneg.mpr
        linarith
      · linarith

  have B_diam' : ∀ n : ℕ, diam (B n) ≤ 1/(n + 1) := by
    intro n
    by_cases! h : diam (B n) = -1
    · rw [h]
      trans 0
      · linarith
      · apply one_div_nonneg.mpr ?_
        linarith
    · unfold diam
      dsimp
      split_ifs with h'
      · apply csSup_le
        · use 0
          use c n
          have h'' : EspaceMetrique.d (c n) (c n) = 0 := by
            rw [EspaceMetrique.is_dist.sep (c n) (c n)]
          exact ⟨c_B n, c n, c_B n, h''⟩
        · simp
          intro d x hx y hy h
          have h_dist : ∀ z : X, z ∈ B n → EspaceMetrique.d z (c n) ≤ (min (r n) (1 / (2*(↑n + 1))))
          := by
            intro z hz
            simp only [boule_fermee, one_div, mul_inv_rev, le_inf_iff, mem_setOf_eq, B] at hz
            simp only [one_div, mul_inv_rev, le_inf_iff]
            exact ⟨hz.1, by apply hz.2.trans; rfl⟩
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
    unfold converges_to
    intro ε ε_pos
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt ε_pos
    use N
    intro n hn
    change |((fun n ↦ diam (B n)) n) - 0| ≤ ε
    simp only [sub_zero]
    specialize B_diam' n
    rcases diam_nneg (B n) with h | h
    · rw [abs_le]
      constructor
      · linarith
      · apply B_diam'.trans
        apply le_of_lt at hN
        trans 1 / (↑N + 1)
        · gcongr
        · exact hN
    · have B_in_boule : in_boule (B n) := by
        use (c n), 2*(r n)
        constructor
        · simp
          exact r_pos n
        · unfold B
          simp
          exact fun _ hx _ ↦ lt_of_le_of_lt hx (lt_two_mul_self (r_pos n))
      rw [←bdd_iff_in_boule, ←bornee_iff_bdd] at B_in_boule
      unfold diam_bornee at B_in_boule
      have nh : diam (B n) ≠ -1 := ne_of_gt B_in_boule.2
      contradiction

  have W_decrois : ∀ n : ℕ, W (n + 1) ⊆ W n := by
    intro n
    unfold W
    apply Set.inter_subset_inter_right
    apply Set.biInter_subset_biInter_left
    intro k hk
    exact ⟨hk.1, Nat.le_succ_of_le hk.2⟩

  apply thm_beurre X_compl at B_diam

  swap
  · intro n
    constructor
    · rw [← Set.nonempty_iff_ne_empty]
      exact ⟨c n, c_B n⟩
    · constructor
      · apply fer_of_boule_fer
      · apply crois_equ.mpr
        intro m
        sorry

  rcases B_diam with ⟨x, hx⟩



  --B_W B_diam W_decrois

  sorry
