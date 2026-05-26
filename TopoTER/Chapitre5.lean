import TopoTER.Chapitre4
set_option linter.style.emptyLine false

open TER Set EspTop

variable {X : Type}

lemma crois_equ {F : ℕ → Set X} :
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

lemma lemme1 {U : ℕ → Set X} : ⋂ n, U n = ⋂ n, ⋂ k ∈ Icc 0 n, U k := by
  ext x
  simp only [mem_Icc, zero_le, true_and, mem_iInter]
  exact ⟨fun h _ m _ ↦ h m, fun h n ↦ h n n (by simp)⟩

lemma lemme2 {V : Set X} {U : ℕ → Set X} :
V ∩ ⋂ n, ⋂ k ∈ Icc 0 n, U k = ⋂ n, V ∩ ⋂ k ∈ Icc 0 n, U k := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  exact ⟨fun h n ↦ ⟨h.1, h.2 n⟩, h ↦ ⟨(h 0).1, fun n m hm ↦ (h n).2 m hm⟩⟩

lemma lemme3 {n : ℕ} : Set.Icc 0 (n + 1) = insert (n + 1) (Set.Icc 0 n) := by
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

-----------------------------------------------------------------------------------------

variable [EspTop X]

lemma conv_ge_N_equ {u : ℕ → X} {v : ℕ → X} {l : X} {N : ℕ} :
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

def prop_baire (u : ℕ → Set X) := (∀ (n : ℕ),
  dense X (u n) ∧ est_ouvert (u n)) → dense X (⋂ n : ℕ, u n)

def baire (X : Type) [EspTop X] : Prop := ∀ (u : ℕ → Set X), prop_baire u

open Metrique

variable {X Y : Type} [EspaceMetrique X] [EspaceMetrique Y]

lemma conv_to_equ {u : ℕ → X} {l : X} : converge_vers u l ↔ converges_to u l := by
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

lemma conv_equ {u : ℕ → X} : converge u ↔ converges u := by
  unfold converge converges
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, conv_to_equ.mp hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l, conv_to_equ.mpr hl⟩

lemma cauchy_unif_continu_cauchy (f : X → Y)
(hcont : unif_continu f) (u : ℕ → X) (h : cauchy u) : cauchy (f ∘ u) := by
  intro ε ε_pos
  rcases hcont ε ε_pos with ⟨δ, ⟨hδ_pos, hconvδ⟩⟩
  specialize h δ hδ_pos
  rcases h with ⟨N, hnN⟩
  exact ⟨N, fun m hm n hn ↦ hconvδ (u m) (u n) (hnN m hm n hn)⟩

theorem prolongement_unif_continu (A : Partie X) (f : A → Y) (hf : unif_continu f)
(hY : complet Y) :
∃! (g : adh A → Y), (∀ x : A, f x = g ⟨x.1, contenu_adh A x.2⟩) ∧ unif_continu g := by

    have cvg_in_Y : ∀ u : ℕ → A, cauchy u → converges (f ∘ u) := by
      intro u hu
      have cauchyf : cauchy (f ∘ u) := cauchy_unif_continu_cauchy f hf u hu
      exact hY (f ∘ u) cauchyf

    have suite_conv : ∀ x : adh A, ∃ u : ℕ → A, converge_vers (fun n ↦ ⟨u n, contenu_adh A (u n).2⟩) x := by
      intro x
      rcases (in_adh_suite A x).mp x.2 with ⟨u, u_A, hu⟩
      have : ∀ (n : ℕ), u n ∈ adh A := n ↦ contenu_adh A (u_A n)
      use (fun n ↦ ⟨u n, u_A n⟩)
      intro V V_vois
      rcases V_vois with ⟨v, x_v, v_ouv, v_V⟩
      rcases v_ouv with ⟨w, w_ouv, w_v⟩
      have segolene : est_vois (↑x) w := by
        use w
        constructor
        · rw [w_v] at x_v
          exact x_v
        · exact w_ouv
        · exact subset_refl w
      rcases hu w segolene with ⟨N, hN⟩
      use N
      intro n hn
      simp
      apply v_V
      rw [w_v]
      exact hN n hn





  --  have eeeeeeeee : ∀ x : adh A, ∃ l : Y, ∀ u : ℕ → A, (converge_vers (fun n => (u n : X)) (x : X))
  --    → converges_to (f ∘ u) l := by
  --    intro x
  --    rcases suite_conv x with ⟨y', hy1, hy2⟩
  --    have hy3 : converges y' := by
  --      rw [←conv_equ]
  --      use x
  --    let y : ℕ → ↑A := fun n ↦ ⟨y' n, hy1 n⟩
  --    rcases cvg_in_Y y (cauchy_of_conv y' hy3) with ⟨l, hl⟩
  --    use l
  --    intro u u_conv
  --    sorry

    have unicite_lim : ∀ x : adh A, ∀ u v : ℕ → A, ((converges_to (fun n => (u n : X)) (x : X)) ∧ (converges_to (fun n => (v n : X)) (x : X)))
      → ∃ l : Y,  (converges_to (f ∘ u) l  ∧ converges_to (f ∘ v) l) := by
        intro x u v ⟨hu, hv⟩
        let z : ℕ → ↑A := n ↦ if Even n then u n else v n
        -- 1. On définit la version "étendue" de z dans X
        let z_X := fun n ↦ (z n : X)
        have z_conv : converges z_X := by
          use x
          intro ε ε_pos
          rcases hu ε ε_pos with ⟨N, hN⟩
          rcases hv ε ε_pos with ⟨M, hM⟩
          use max N M
          intro n hn
          by_cases! pair : Even n
          · unfold z_X z
            simp [pair]
            exact hN n (le_of_max_le_left hn)
          · unfold z_X z
            simp [pair]
            exact hM n (le_of_max_le_right hn)
        -- 2. On prouve qu'elle est Cauchy dans X (car elle y converge vers x)
        have cauchy_z_X : cauchy z_X := cauchy_of_conv z_X z_conv

        -- 3. On montre que cauchy z_X est identique à cauchy z
        -- (En Lean, c'est vrai par définition car la distance est la même)
        have cauchy_z : cauchy z := cauchy_z_X

        --have cauchy_z : cauchy z := cauchy_of_conv z z_conv
        have lil_z : converges (f∘z) := cvg_in_Y z cauchy_z
        rcases lil_z with ⟨l, hl⟩
        use l
        sorry
        --constructor
        --· have conv_fu : converges (f ∘ u) := cvg_in_Y u (cauchy_of_conv_to hu)

    have conv_u_fu : ∀ u : ℕ → A, converges u → converges (f ∘ u) :=
      fun u h ↦ hY (f ∘ u) (cauchy_unif_continu_cauchy f hf u (cauchy_of_conv u h))

    let g := fun x ↦ Classical.choose (suite_conv x)

    sorry

lemma diam_born_sub {A B : Partie X} :
diam_bornee B → A ⊆ B → diam_bornee A := by
  intro bornB A_B
  rw [bornee_iff_bdd]
  rw [bornee_iff_bdd] at bornB
  unfold dist_bornee
  unfold dist_bornee at bornB
  rcases bornB with ⟨M, hM⟩
  exact ⟨M,
  fun x hx y hy ↦ hM x (Set.mem_of_mem_of_subset hx A_B) y (Set.mem_of_mem_of_subset hy A_B)⟩

lemma diam_crois {A B : Partie X} :
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

-----------------------------------------------------------------------------------------

lemma diam_0_singl_or_empty {A : Partie X} :
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

lemma lemme {F : ℕ → Partie X} {x : ℕ -> X} :
(∀ n : ℕ, x n ∈ F n) → (∀ n m : ℕ, m ≥ n → (F m) ⊆ (F n)) → converges_to (fun n ↦ diam (F n)) 0 →
cauchy x := by
  intro x_F F_decrois diam0 e e_pos
  let ε := min e 0.5
  have ε_1 : ε < 1 := lt_of_le_of_lt (min_le_right e 0.5) (by linarith)
  rcases diam0 ε (lt_min e_pos (by norm_num)) with ⟨N, hN⟩
  simp only at hN
  change ∀ n ≥ N, |diam (F n) - 0| ≤ ε at hN
  use N
  intro n hn m hm
  let M : ℕ := min n m
  have hM : M ≥ N := Nat.le_min_of_le_of_le hn hm
  specialize hN M (Nat.le_min_of_le_of_le hn hm)
  simp only [sub_zero] at hN
  have diam_pos : diam (F M) ≥ 0 := by
    rcases diam_nneg (F M) with h | h
    · exact h
    · have : diam (F M) ≠ -1 := heq ↦ (by simp [heq] at hN; linarith)
      contradiction
  rw [abs_of_nonneg diam_pos] at hN
  have hyp_le : EspaceMetrique.d (x n) (x m) ≤ diam (F M) := by
    unfold diam at *
    dsimp at diam_pos
    split_ifs at diam_pos with h
    · rw [if_pos h]
      apply le_csSup h
      simp only [Set.mem_setOf_eq]
      exact ⟨x n, Set.mem_preimage.mp ((F_decrois M) _ (Nat.min_le_left n m) (x_F n)), x m,
      Set.mem_preimage.mp ((F_decrois M) _ (Nat.min_le_right n m) (x_F m)), by rfl⟩
    · linarith
  exact le_trans (le_trans hyp_le hN) (min_le_left e 0.5)

theorem pre_thm_baire {F : ℕ → Partie X} : complet X →
(∀ n : ℕ, (F n).Nonempty) → (∀ n : ℕ, fermee (F n)) → (∀ n m : ℕ, m ≥ n → (F m) ⊆ (F n)) →
converges_to (fun n ↦ diam (F n)) 0 -> ∃ x : X, ⋂ n : ℕ, F n = {x} := by
  intro compl F_ne F_fer F_decrois lim
  have h : ∀ n : ℕ, ∃ x : X, x ∈ F n := fun n ↦ F_ne n
  choose x hx using h

  have x_cau : cauchy x := lemme hx F_decrois lim

  rcases compl x x_cau with ⟨l, hl⟩

  have hF : ∀ n : ℕ, ∀ m : ℕ, m ≥ n → x m ∈ F n := by
    intro n m hm
    exact (F_decrois n) m hm (hx m)

  have lfn : l ∈ ⋂ n : ℕ, F n := by
    rw [mem_iInter]
    intro N
    specialize F_fer N
    change est_ferme (F N) at F_fer
    rw [ferme_iff_adh] at F_fer
    rw [←F_fer, in_adh_suite]
    let y : ℕ → X := n ↦ if n < N then x N else x n
    use y
    constructor
    · intro n
      by_cases n_N : n < N
      · simp only [n_N, ↓reduceIte, y]
        exact hF N N (by rfl)
      · simp only [n_N, ↓reduceIte, y]
        push_neg at n_N
        exact hF N n n_N
    · have x_eq_y : ∀ n ≥ N, x n = y n := by
        intro n hn
        simp [y, hn]
      rw [←conv_ge_N_equ x_eq_y, conv_to_equ]
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

theorem thm_baire : complet X → baire X := by
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
      rw [lemme3, biInter_insert]
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
      rcases hU (n + 1) with ⟨U_dens, _⟩
      have ne : (Bₒ p.1 p.2 ∩ U (n + 1)).Nonempty :=
        (dense_iff_inter_ouvert_nonempty (U (n + 1))).mp U_dens (Bₒ p.1 p.2)
        (ouv_of_boule_ouv p.1 p.2) ⟨p.1, centre_in_boule p.1 r_pos⟩
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
      have next : B_ok (n + 1) (c_next, r_next).1 (c_next, r_next).2 := by
        constructor
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
            rw [lemme3, Set.biInter_insert, inter_comm (U (n + 1)), ←inter_assoc]
            exact inter_subset_inter (subset_trans (boule_in_boule_f p.1 r_pos) h) (by rfl)
      exact ⟨next, subset_trans hyp (subset_trans inter_subset_left (boule_in_boule_f p.1 r_pos))⟩

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
        have h' : ∀ z : X, z ∈ B n → EspaceMetrique.d z (c n) ≤ (min (r n) (1 / (2*(↑n + 1)))) := by
          intro z hz
          simp only [boule_fermee.eq_1, mem_setOf_eq, B] at hz
          simp only [one_div, mul_inv_rev, le_inf_iff]
          specialize Bn_ok n
          rcases Bn_ok with ⟨h1, h2, h3⟩
          have h_calc : 1 / (2 * ((n : ℝ) + 1)) = ((n : ℝ) + 1)⁻¹ * 2⁻¹ := by field_simp
          rw [←h_calc]
          exact ⟨hz, hz.trans h2⟩
        rw [←h]
        calc EspaceMetrique.d x y
          ≤ EspaceMetrique.d x (c n) + EspaceMetrique.d (c n) y :=
            EspaceMetrique.is_dist.ineq x (c n) y
          _ ≤ (min (r n) (1 / (2*(↑n + 1)))) + (min (r n) (1 / (2*(↑n + 1)))) :=
            add_le_add (h' x hx) (by rw [EspaceMetrique.is_dist.symm]; exact (h' y hy))
          _ = 2 * (min (r n) (1 / (2*(↑n + 1)))) := by ring
          _ ≤ 2 * (1 / (2*(↑n + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
          _ ≤ (↑n + 1)⁻¹ := by field_simp; rfl
    · trans 0
      · linarith
      · exact one_div_nonneg.mpr (by linarith)

  have B_diam : converges_to (n ↦ (diam (B n))) 0 := by
    exact conv_of_le_inv (n ↦ diam (B n)) B_diam_pos B_diam_le_inv

  apply pre_thm_baire X_compl (n ↦ ⟨c n, c_B n⟩) (n ↦ fermee_of_boule_f (c n) (r n))
    (crois_equ.mpr (n ↦ bf_in_bf n)) at B_diam

  rcases B_diam with ⟨x, hx⟩
  have h : (⋂ n, B n).Nonempty := by
    use x
    rw [hx]
    rfl
  have B_W  : ⋂ n, B n ⊆ ⋂ n, V ∩ ⋂ k ∈ Icc 0 n, U k := Set.iInter_mono (n ↦ (Bn_ok n).2.2)
  rw [lemme1, lemme2]
  exact Nonempty.mono B_W h

-----------------------------------------------------------------------------------------

variable {X Y : Type} [EspTop X]

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

--mardi 26 mai a 15h avec un thm chacun (1/2 heure chacun)
--nettoyer le code quitte a mettre des sorry
--rapport même si c'est pas mega complet, surtout il faut qu'il y ait ce qu'on presente mardi
