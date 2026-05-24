import TopoTER.Chapitre5

open TER Set EspTop

-- 6. Espaces topologiques compacts

variable {X Y : Type} [EspTop X] [EspTop Y] [EspSepareT2 X] [EspSepareT2 Y]

-- 6.1. Compacité via les recouvrements

open Famille

-- a)

@[simp] def couvrement (F : Famille X) (A : Partie X) := A ⊆ ⋃ᵢ F

@[simp] def sous_couvrement (F : Famille X) (J : Set F.ι) (A : Partie X) :=
  couvrement (SousFamille F J) A

omit [EspTop X] in
lemma sous_couvre_of_couvre (F : Famille X) (A : Partie X) (h : couvrement F A) :
  sous_couvrement F Ω A := by
  intro x hx; rw [mem_union_famille]
  rcases h hx with ⟨B, ⟨i, hi⟩, x_in⟩
  use B, (by use ⟨i, by simp⟩), x_in

def est_compact (A : Partie X) := ∀ C : Famille X, (∀ P ∈ C, est_ouvert P)
  → couvrement C A → ∃ J, J.Finite ∧ sous_couvrement C J A

class EspCompact (X : Type) [EspTop X] [EspSepareT2 X] where
  compact : est_compact (X := X) Ω

-- b)

def est_compact_f (X : Type) [EspTop X] [EspSepareT2 X] := ∀ F : Famille X,
  (∀ A ∈ F, est_ferme A) → ⋂ᵢ F = ∅ → ∃ J, J.Finite ∧ ⋂ᵢ (SousFamille F J) = ∅

lemma compact_iff_comp_f : EspCompact X ↔ est_compact_f X := by
  apply Iff.intro
  · intro ⟨comp⟩ F h₁ h₂
    have F_ouvert : ∀ A ∈ F`ᶜ, est_ouvert A := by
      intro A hA; rw [est_ouvert_iff_compl_est_ferme]
      rw [in_compl_famille] at hA; exact h₁ Aᶜ hA
    have F_couvre : couvrement F`ᶜ Ω := by
      simp [←inter_famille_compl, h₂]
  --
    rcases comp F`ᶜ F_ouvert F_couvre with ⟨J, hJ, J_couvre⟩
    use J, hJ; dsimp at J_couvre
    rw [←compl_of_sous_famille, ←inter_famille_compl] at J_couvre
    rwa [univ_subset_iff, compl_univ_iff] at J_couvre
--
  · intro h; constructor; intro F h₁ h₂
    have F_ferme : ∀ A ∈ F`ᶜ, est_ferme A := by
      intro A hA; rw [est_ferme]
      rw [in_compl_famille] at hA; exact h₁ Aᶜ hA
    have F_inter : ⋂ᵢ F`ᶜ = ∅ := by
      simp_all [←union_famille_compl]
    rcases h F`ᶜ F_ferme F_inter with ⟨J, hJ, J_inter⟩; use J, hJ
    rw [←compl_of_sous_famille, ←union_famille_compl] at J_inter
    dsimp; rwa [univ_subset_iff, ←compl_empty_iff]

-- 6.2.

-- a)

open Set.Notation in
instance comp_induite_of_comp {A : Partie X} {comp : est_compact A} :
  EspCompact (Induite A) where
  compact := by
    rw [←self_induite]; intro F F_ouvert F_couvre
    have exists_ouv : ∀ i : F.ι, ∃ U, est_ouvert U ∧ F.u i = A ↓∩ U := by
      intro i; rcases F_ouvert (F.u i) (by use i) with ⟨U, hU⟩
      use U, hU.1, hU.2
    choose! f hf using exists_ouv
--
    let C : Famille X := ⟨F.ι, f⟩
    have C_ouvert : ∀ P ∈ C, est_ouvert P := by
      intro P hP; rcases hP with ⟨i, hi⟩
      dsimp at hi; rw [←hi]; exact (hf i).left
    have C_couvre : couvrement C A := by
      intro x hx; rw [mem_union_famille]; let X : A := ⟨x, hx⟩
      rcases F_couvre X.prop with ⟨B, ⟨i, hi⟩, X_in⟩
      use C.u i, (by use i); dsimp at hi; rwa [←hi, (hf i).2] at X_in
--
    rcases comp C C_ouvert C_couvre with ⟨J, hJ, J_couvre⟩
    use J, hJ; intro x hx; rw [mem_union_famille]
    rcases J_couvre hx with ⟨B, ⟨i, hi⟩, x_in⟩
    use F.u i, (by use i); dsimp [C] at hi; rwa [(hf i).2, hi]

open Set.Notation in
theorem comp_iff_comp_induite (A : Partie X) : EspCompact (Induite A) ↔
  est_compact A := by
  apply Iff.intro
  · case mp => intro ⟨h⟩ C C_ouvert C_couvre
               let F : Famille A := ⟨C.ι, i ↦ A ↓∩ C.u i⟩
               have F_ouvert : ∀ P ∈ F, est_ouvert P := by
                intro P hP; rcases hP with ⟨i, hi⟩
                dsimp [F] at hi; rw [←hi]; use C.u i
                apply And.intro _ (refl _); apply C_ouvert; use i
               have F_couvre : couvrement F Ω := by
                intro x hx; rw [←self_induite] at hx
                rcases C_couvre hx with ⟨B, ⟨i, hi⟩, x_in⟩
                dsimp at hi; rw [mem_union_famille]
                use (A ↓∩ C.u i), (by use i); rwa [←hi] at x_in
--
               rcases h F F_ouvert F_couvre with ⟨J, hJ, J_couvre⟩
               use J, hJ; intro x hx; rw [mem_union_famille]
               let X : A := ⟨x, hx⟩; rw [←self_induite] at J_couvre
               rcases J_couvre X.prop with ⟨B, ⟨i, hi⟩, X_in⟩
               use C.u i, (by use i); dsimp at hi; rwa [←hi] at X_in
  · case mpr => intro h; apply comp_induite_of_comp; exact h

-- b)

theorem inter_decr_non_vide [cmp : EspCompact X] (u : ℕ → Partie X) (hf : ∀ i,
  est_ferme (u i)) (decr : ∀ i, u (i + 1) ⊆ u i) (h : ∀ i, u i ≠ ∅) :
  ⋂ i, u i ≠ ∅ := by
  intro vide; let F : Famille X := ⟨ℕ, u⟩
  have F_ferme : ∀ A ∈ F, est_ferme A := by
    intro A hA; rcases hA with ⟨i, hi⟩
    dsimp at hi; rw [←hi]; exact hf i
  have F_inter : ⋂ᵢ F = ∅ := by rw [←vide]; rfl
--
  rw [compact_iff_comp_f] at cmp
  rcases cmp F F_ferme F_inter with ⟨J, hJ, J_inter⟩
  rcases Finite.bddAbove hJ with ⟨M, hM⟩
  have non_vide : ∃ x, x ∈ F.u (M + 1) := by
    apply Set.nonempty_iff_ne_empty.mpr; apply h
  have of_decr : ∀ n, ∀ i < n, u n ⊆ u i := by
    rw [eq_forall_iff_eq_add_one]
    · intro n; exact decr n
    · intro _ _ _ h₁ h₂; exact subset_trans h₂ h₁
--
  rcases non_vide with ⟨x, hx⟩
  rw [←mem_empty_iff_false x, ←J_inter, mem_inter_famille]
  intro A hA; rcases hA with ⟨i, hi⟩; dsimp at hi; rw [←hi]
  have ineq : i < M + 1 := by
    apply Nat.lt_succ_of_le; exact hM i.prop
  apply of_decr (M + 1) i ineq; exact hx

-- Théorème 6.4.

-- a)

theorem ferme_of_compact {A : Partie X} (h : est_compact A) : est_ferme A := by
  rw [est_ferme, ouvert_ssi_vois]; intro x hx
  have sep_y : ∀ y ∈ A, ∃ U V, est_ouvert U ∧ est_ouvert V ∧ y ∈ U ∧ x ∈ V
    ∧ U ∩ V = ∅ := by
    intro y hy; expose_names; apply inst_1.est_separe y x
    intro eq; rw [eq] at hy; exact hx hy
  choose! u v hu hv y_in x_in disj using sep_y
--
  let F : Famille X := ⟨A, y ↦ u y⟩
  have F_ouvert : ∀ P ∈ F, est_ouvert P := by
    intro P hP; rcases hP with ⟨y, hy⟩
    rw [←hy]; exact hu y y.prop
  have F_couvre : couvrement F A := by
    intro y hy; rw [mem_union_famille]
    use u y, (by use ⟨y, hy⟩); exact y_in y hy
  rcases h F F_ouvert F_couvre with ⟨J, hJ, J_couvre⟩
--
  let V' := ⋂ j ∈ J, v j; use V'; constructor
  · simp only [V', mem_iInter]; intro j hj
    exact x_in j j.prop
  · unfold V'; apply inter_fini_ouvert (hI := hJ)
    intro j hj; exact hv j j.prop
  · intro z hz in_A
    rcases J_couvre in_A with ⟨j, ⟨y, hy⟩, z_in⟩
    rw [←mem_empty_iff_false z, ←disj y y.val.prop]
    apply And.intro
    · dsimp [F] at hy; rwa [hy]
    · rw [←hy] at z_in; rw [mem_iInter] at hz
      apply hz y; use y.prop

-- b)

theorem compact_of_ferme [EspCompact X] {A : Partie X} (h : est_ferme A)
  : est_compact A := by sorry

-- Théorème 6.5.

omit [EspSepareT2 X] in
theorem compact_of_continu_image {f : X → Y} (h : est_continu f) {A : Partie X}
  (comp : est_compact A) : est_compact (f '' A) := by
  intro C h₁ h₂
  let F : Famille X := ⟨C.ι, i ↦ f ⁻¹' (C.u i)⟩
  have F_ouvert : ∀ A ∈ F, est_ouvert A := by
    intro A hA; rcases hA with ⟨i, hi⟩; dsimp [F] at hi
    rw [continu_iff_preim_ouv] at h; rw [←hi]
    apply h; apply h₁; use i
  have F_couvre : couvrement F A := by
    intro x x_in; rw [mem_union_famille]
    have in_image : f x ∈ f '' A := by use x
    apply h₂ at in_image; rcases in_image with ⟨B, ⟨i, hi⟩, fx_in⟩
    use f ⁻¹' B; apply And.intro _ fx_in; use i; simp [F, hi]
--
  rcases comp F F_ouvert F_couvre with ⟨J, hJ, J_couvre⟩
  use J, hJ; intro y y_in; rcases y_in with ⟨x, x_in, hx⟩
  apply J_couvre at x_in; rcases x_in with ⟨s, s_in, hs⟩
  rcases s_in with ⟨i, hi⟩; rw [←hi] at hs
  rw [mem_union_famille]; use C.u i, (by use i), (by rwa [←hx])

-- 6.2. Espaces métriques compacts

open Metrique

variable {E F : Type} [M₁ : EspaceMetrique E] [M₂ : EspaceMetrique F]

-- Proposition 6.7.

theorem borne_of_compact {A : Partie E} (h : est_compact A) : est_borne A := by
  let C : Famille E := ⟨E, x ↦ Bₒ x 1⟩
  have C_ouvert : ∀ A ∈ C, est_ouvert A := by
    intro A hA; rcases hA with ⟨x, hx⟩
    dsimp [C] at hx; rw [←hx]; unfold est_ouvert;
    exact ouv_of_boule_ouv x 1
  have C_couvre : couvrement C A := by
    intro x hx; rw [mem_union_famille]; use Bₒ x 1, (by use x)
    exact centre_in_boule x one_pos
--
  rcases h C C_ouvert C_couvre with ⟨J, hJ, J_couvre⟩
  let S := {d(x, y) | (x ∈ J) (y ∈ J)}
  have bdd : BddAbove S := by
    let f : E × E → ℝ := I ↦ d(I.1, I.2)
    apply Set.Finite.bddAbove
    apply Set.Finite.of_surjOn f (s := J ×ˢ J)
    · intro s hs; rcases hs with ⟨x, hx, y, hy, hs⟩
      use (x, y), (mem_prod.mp ⟨hx, hy⟩), hs
    · exact Set.Finite.prod hJ hJ
  rcases bdd with ⟨M, hM⟩; unfold est_borne
  rw [←bdd_iff_bdd_by_nneg]; use M + 2; intro x hx y hy
--
  rcases J_couvre hx with ⟨A, ⟨i, hi⟩, x_in⟩
  rcases J_couvre hy with ⟨B, ⟨j, hj⟩, y_in⟩
  have ineq₁ := M₁.is_dist.ineq x i.val y
  have ineq₂ := M₁.is_dist.ineq i.val j.val y
  have d_ij_in : d(i.val, j.val) ∈ S := by
    use i.val, i.prop, j.val, j.prop
  have ineq₃ := hM d_ij_in
  rw [←hi] at x_in; dsimp [C] at x_in; rw [←hj] at y_in
  dsimp [C] at y_in; rw [M₁.is_dist.symm] at y_in; linarith

-- Définition 6.8.

def ε_precompact (E : Type) [EspaceMetrique E] (ε : ℝ) := ∃ F : Famille E,
  Finite F.ι ∧ (∀ A ∈ F, ∃ x, A = Bₒ x ε) ∧ couvrement F Ω

def precompact (E : Type) [EspaceMetrique E] := ∀ ε > 0, ε_precompact E ε

def lebesgue_n (F : Famille E) (r : ℝ) := ∀ x, ∃ A ∈ F, Bₒ x r ⊆ A

def has_lebesgue_n (F : Famille E) := ∃ r > 0, lebesgue_n F r

def seq_compact (E : Type) [EspaceMetrique E] := ∀ u : ℕ → E, ∃ φ,
  extraction φ ∧ converges (u ∘ φ)

def lebesgue_compact (E : Type) [EspaceMetrique E] := ∀ F : Famille E,
  (∀ A ∈ F, est_ouvert A) → couvrement F Ω → has_lebesgue_n F

-- Théorème 6.9.

lemma exists_next_of_not_precomp {ε : ℝ} (h : ¬ε_precompact E ε) (n : ℕ)
  (u : Fin n → E) : ∃ x, ∀ i, d(x, u i) ≥ ε := by
  contrapose h; push_neg at h
  let F : Famille E := ⟨Fin n, i ↦ Bₒ (u i) ε⟩
  use F, (by apply Finite.of_fintype); apply And.intro
  · intro A hA; rcases hA with ⟨i, hi⟩
    dsimp at hi; use (u i); rw [←hi]
  · intro x hx; rcases h x with ⟨i, hi⟩
    rw [mem_union_famille]; use (F.u i), (by use i), hi

lemma precompact_of_empty (h : IsEmpty E) : precompact E := by
  intro ε ε_pos
  let F : Famille E := ⟨E, x ↦ Bₒ x ε⟩; use F
  apply And.intro
  · have fin := @Fintype.ofIsEmpty E h
    apply Finite.of_fintype
  · apply And.intro
    · intro A hA; rcases hA with ⟨x, hx⟩
      use x, by rw [←hx]
    · intro x hx; apply @IsEmpty.elim E h

lemma exists_next_of_no_lebesgue (F : Famille E) (h : ¬has_lebesgue_n F) (n : ℕ) :
  ∃ x, ∀ A ∈ F, ¬Bₒ x (1/(n+1)) ⊆ A := by
  contrapose h; push_neg at h
  use 1/(n+1), (by field_simp; linarith), h

lemma lebesgue_compact_of_empty (h : IsEmpty E) : lebesgue_compact E := by
  intro F F_ouvert F_couvre; use 1, one_pos
  apply @IsEmpty.elim E h

theorem seq_comp_of_compact (E : Type) [EspaceMetrique E] : EspCompact E →
  seq_compact E := by
  intro h u; let X := k ↦ {x : E | ∃ n ≥ k, u n = x}
  suffices h : ⋂ n : ℕ, adh (X n) ≠ ∅ by
    rw [←val_adh_inter, ←Set.nonempty_iff_ne_empty] at h
    rcases h with ⟨x, hx⟩; dsimp at hx
    rw [val_adh_iff_extraite_conv] at hx
    rcases hx with ⟨φ, hφ, conv⟩
    use φ, hφ, x; rwa [←conv_vers_iff_conv_to]
  apply inter_decr_non_vide
  · intro i; exact adh_ferme
  · intro i; apply adh_contenu_adh; intro x hx
    rcases hx with ⟨n, n_ge, hn⟩; use n, (by linarith), hn
  · intro i h; rw [adh_vide] at h
    rw [←mem_empty_iff_false (u i), ←h]; use i

theorem lebesgue_comp_of_seq_comp (E : Type) [EspaceMetrique E] : seq_compact E →
  precompact E ∧ lebesgue_compact E := by
  intro seq_comp; apply And.intro
  · by_cases nonempty : Nonempty E
    · case pos => intro ε ε_pos; by_contra contra
                  let P (x y : E) := d(y, x) ≥ ε
                  have next := exists_next_of_not_precomp contra
                  rcases exists_by_piecewise P nonempty next with ⟨u, hu⟩
                  rcases seq_comp u with ⟨φ, hφ, conv⟩
                  apply cauchy_of_conv at conv
                  rcases conv (ε/2) (by linarith) with ⟨N, hN⟩
                  specialize hN (N+1) (by linarith) N (refl N)
                  absurd hN; rw [not_le]
                  apply lt_of_lt_of_le (half_lt_self ε_pos)
                  apply hu; apply hφ; linarith
    · case neg => rw [not_nonempty_iff] at nonempty
                  exact precompact_of_empty nonempty
--
  · by_cases nonempty : Nonempty E
    · case pos => intro F F_ouvert F_couvre; by_contra contra
                  choose! f hf using (exists_next_of_no_lebesgue F contra)
                  rcases seq_comp f with ⟨φ, hφ, ⟨l, conv_l⟩⟩
                  rcases F_couvre (mem_univ l) with ⟨L, hL, l_in⟩
                  rcases F_ouvert L hL l l_in with ⟨ε, ε_pos, hε⟩
                  rcases conv_l (ε/2) (by linarith) with ⟨N₁, hN₁⟩
                  rcases inv_of_le_forall (ε/2) (by linarith) with ⟨N₂, hN₂⟩
--
                  let N := max N₁ N₂; apply hf (φ N) L hL; intro x hx
                  have ineq₁ : d(x, f (φ N)) < ε/2 := by
                    apply lt_of_lt_of_le hx; apply hN₂
                    apply le_trans _ (n_le_extr_n hφ N); apply le_max_right
                  have ineq₂ : d(f (φ N), l) ≤ ε/2 := hN₁ N (le_max_left N₁ N₂)
                  have ineq₃ := EspaceMetrique.is_dist.ineq x (f (φ N)) l
                  apply hε; apply lt_of_le_of_lt ineq₃; linarith
    · case neg => rw [not_nonempty_iff] at nonempty
                  exact lebesgue_compact_of_empty nonempty

theorem compact_of_lebesgue_comp (E : Type) [EspaceMetrique E] : precompact E ∧
  lebesgue_compact E → EspCompact E := by
  intro ⟨h₁, h₂⟩; constructor; intro C C_ouvert C_couvre
  by_cases nonempty : Nonempty C.ι
  · case pos => rcases h₂ C C_ouvert C_couvre with ⟨r, r_pos, hr⟩
                rcases h₁ r r_pos with ⟨J, J_fin, hJ, J_couvre⟩
                have sousF : ∀ j : J.ι, ∃ i : C.ι, J.u j ⊆ C.u i := by
                  intro j; rcases hJ (J.u j) (by use j) with ⟨x, hx⟩
                  rw [hx]; rcases hr x with ⟨A, ⟨i, hi⟩, incl_A⟩
                  use i; dsimp at hi; rwa [hi]
                choose! f hf using sousF; use Set.range f; apply And.intro
                · apply SupReal.image_of_fin
                · intro x hx; rcases J_couvre hx with ⟨B, ⟨j, hj⟩, x_in⟩
                  rw [mem_union_famille]; use C.u (f j); apply And.intro
                  · use ⟨f j, by use j⟩
                  · apply hf; dsimp at hj; rwa [hj]
  · case neg => rw [not_nonempty_iff] at nonempty
                use Ω; apply And.intro
                · have fin := @Fintype.ofIsEmpty C.ι nonempty
                  apply Finite.of_fintype
                · exact sous_couvre_of_couvre C Ω C_couvre

theorem compact_iff_seq_comp (E : Type) [EspaceMetrique E] : EspCompact E ↔
  seq_compact E := by
  apply Iff.intro (seq_comp_of_compact E)
  intro hyp; apply compact_of_lebesgue_comp
  exact lebesgue_comp_of_seq_comp E hyp

-- Corollaire 6.10.

theorem compact_iff_ferme_borne (A : Partie ℝ) : est_compact A ↔ est_ferme A ∧
  est_borne A := by
  apply Iff.intro
  · case mp => intro h; apply And.intro
               · exact ferme_of_compact h
               · exact borne_of_compact h
  · case mpr => intro ⟨hf, hb⟩; rw [←comp_iff_comp_induite]
                suffices h : seq_compact (Induite A) by
                  rw [←compact_iff_seq_comp] at h; constructor
                  have cmp := h.compact; intro C C_ouvert C_couvre
                  have C_ouvert' :
                        ∀ P ∈ C, instOfEspaceMetrique.est_ouvert P := by
                    intro P hP; rw [←ouv_of_ind_iff_ouv_of_metrique_ind]
                    exact C_ouvert P hP
                  rcases cmp C C_ouvert' C_couvre with ⟨J, hJ, J_couvre⟩
                  use J, hJ, J_couvre
--
                intro u; rcases hb with ⟨M, M_nneg, hM⟩
                let u' : ℕ → ℝ := n ↦ u n
                have seq_bdd : seq_bornee u' := by
                  use M, M_nneg; intro x hx y hy; apply hM
                  · rcases hx with ⟨n, hn⟩; unfold u' at hn
                    rw [←hn]; exact (u n).prop
                  · rcases hy with ⟨n, hn⟩; unfold u' at hn
                    rw [←hn]; exact (u n).prop
                rw [seq_bornee, bornee_iff_bounded] at seq_bdd
                have bdd : ∃ M, ∀ n, |u' n| ≤ M := by
                  rcases seq_bdd with ⟨M, hM⟩; use M
                  intro n; apply hM; use n
                rcases SupReal.bolzano_weierstrass u' bdd with ⟨φ, hφ, conv⟩
--
                use φ, hφ; rw [←conv_iff_really_conv] at conv
                rcases conv with ⟨l, hl⟩
                have hl' := (conv_vers_iff_conv_to (u'∘φ) l).mpr hl
                have in_A : l ∈ A := by
                  rw [ferme_iff_lim_suite] at hf
                  specialize hf (u'∘φ) (n ↦ (u (φ n)).prop) (by use l)
                  rcases hf with ⟨l', conv⟩
                  have l_eq_l' := unicite_lim (u'∘φ) l l' ⟨hl', conv.2⟩
                  rw [l_eq_l']; exact conv.left
                let L : A := ⟨l, in_A⟩; use L; apply hl

-- Exemple 6.12.

-- d)

theorem bornes_atteintes {f : X → ℝ} (h : est_continu f) {A : Partie X}
  (comp : est_compact A) : ∃ a b, ∀ x ∈ A, f x ∈ [a ≤__≤ b] ∧ ∃ x₁ x₂,
  f x₁ = a ∧ f x₂ = b := by
  sorry

-- 6.4. Compacts d'un e.v.n. de dimension finie

open Valuation VectorSpace K_n EspaceNorme

variable {n : ℕ} {K : Type} [ValuationField K]

-- Lemme 6.23.

open EspaceNorme in
lemma norme_Kn_lipschitz {N : K ^ n → ℝ} (h : estNorme (K := K) N) :
  k_lipschitz N := by
  let e (i : Fin n) := canonBasis K i
  cases n
  · case zero => use 1, one_pos; intro x y
                 simp [zero_of_K_zero, self_dist]
  · case succ k =>
    let C := sSup {N (e i) | i}
    have lip_pos : 0 < (k + 1) * C := by
      apply mul_pos (by linarith)
      apply lt_csSup_of_lt (a := N (e 1)) _ (by use 1)
      · apply lt_of_le_of_ne (h.nneg (e 1)); intro eq
        symm at eq; rw [h.definie, eq_zero_iff] at eq
        absurd eq 1; simp [e, canonBasis]
      · apply SupReal.bddabove_of_fin_image
--
    use (k + 1) * C, lip_pos; intro x y
    have ineq₁ : |N x - N y| ≤ N (x - y) := by
      rw [abs_sub_le_iff]; apply And.intro
      · apply sub_ineq h
      · rw [norm_symm h]; apply sub_ineq h
    apply le_trans ineq₁
    let z := x - y; refold_let z
    have ineq₂ : N z ≤ ∑ i, N (z.p i • e i) := by
      nth_rw 1 [inCanonBasis z]
      apply Finset.le_sum_of_subadditive
      · rw [norm_zero h]
      · intro x y; apply h.ineq
    apply le_trans ineq₂
--
    rw [mul_assoc, ←Nat.cast_add_one, ←nsmul_eq_mul]
    nth_rw 10 [←Finset.card_fin (k + 1)]
    apply Finset.sum_le_card_nsmul; intro i hi
    rw [mul_comm, h.homogen]; apply mul_le_mul
    · apply le_csSup _ (by use i)
      apply SupReal.bddabove_of_fin_image
    · apply le_csSup _ (by use i)
      apply SupReal.bddabove_of_fin_image
    · exact h.nneg (e i)
    · exact EspaceMetrique.is_dist.nneg x y

-- Theorème 6.22.

theorem K_norm_equiv {N₁ N₂ : K ^ n → ℝ} (h₁ : estNorme (K := K) N₁)
  (h₂ : estNorme (K := K) N₂) : N₁ ≃ N₂ on K^n := by sorry
