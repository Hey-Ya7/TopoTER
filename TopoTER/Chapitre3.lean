import TopoTER.Chapitre2

open TER Set EspTop Metrique

variable {X Y Z : Type} [EspTop X] [EspTop Y] [EspTop Z] [EspSepareT2 Y]
variable {E F : Type} [M : EspaceMetrique E] [EspaceMetrique F]

def est_continu_point {X Y : Type} [EspTop X] [EspTop Y] (f : X → Y) (x : X) : Prop :=
  ∀(V : Set Y), (est_vois (f x) V) → ∃(U : Set X), (est_vois x U) ∧  (f '' U ⊆ V)

def est_continu {X Y : Type} [EspTop X] [EspTop Y] (f : X → Y) : Prop :=
  ∀(x : X), est_continu_point f x

theorem continu_iff_preim_ouv (f : X → Z) :
  est_continu f ↔ ∀ (V : Set Z), est_ouvert V → est_ouvert (f ⁻¹' V) := by
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

lemma comp_est_continu {X Y Z : Type} [EspTop X] [EspTop Y] [EspTop Z] (f : X → Y)
  (g : Y → Z) (hf : est_continu f) (hg : est_continu g) :
  est_continu (g ∘ f) := by
    rw [continu_iff_preim_ouv] at *
    intro V hV; rw [Set.preimage_comp]
    apply hf; apply hg; exact hV

omit [EspSepareT2 Y] in
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

omit [EspSepareT2 Y] in
theorem continu_iff_preim_ferm (f : X → Y) :
est_continu f ↔ ∀ (F : Set Y), est_ferme F → est_ferme (f ⁻¹' F) := by
  rw[continu_iff_preim_ouv]
  exact continu_ouv_ferm f

omit [EspSepareT2 Y] in
lemma continu_im_adh_in_adh_im (f : X → Y) (A : Set X) : est_continu f →
  f '' (adh A) ⊆ adh (f '' A) := by
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

def unif_continu (f : E → F) := ∀ ε > 0, ∃ δ > 0, ∀ x y : E, d(x, y) ≤ δ
  → d(f x, f y) ≤ ε

def lipschitz (k : ℝ) (f : E → F) := ∀ x y, d(f x, f y) ≤ k * d(x, y)

def k_lipschitz (f : E → F) := ∃ k > 0, lipschitz k f

open Valuation VectorSpace EspaceNorme in
variable {K G : Type} [ValuationField K] [GroupeNorme G] [V : EspaceVecNorme K G] in
--
lemma norme_lipschitz : lipschitz 1 N(K, G) := by
  intro x y; dsimp
  rw [dist_real, one_mul, abs_sub_le_iff]
  apply And.intro
  · apply sub_ineq V.is_norm
  · dsimp; rw [dist_norme, norme_symm V.is_norm]
    apply sub_ineq V.is_norm

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
--
    have y_dist : d(x, y) ≤ δ := by
      simp only [boule_ouverte] at hyB
      rw[Set.mem_setOf] at hyB
      trans δ/2
      · rw [EspaceMetrique.is_dist.symm x y];
        exact le_of_lt hyB
      · linarith
    specialize hf x y y_dist
--
    have fy_in_boule : (f y) ∈ Bₒ (f x) r := by
      dsimp; expose_names; apply lt_of_le_of_lt
      · rw [inst.is_dist.symm (f y) (f x)]
      · calc _ ≤ ε := hf
             _ = r / 3 := by rfl
             _  < r := by linarith
    rw [Set.mem_preimage]
    exact mem_preimage.mp (V_G (hBr fy_in_boule))

lemma lip_continu (f : E → F) : k_lipschitz f → unif_continu f := by
  unfold k_lipschitz unif_continu
  rintro hlip ε ε_pos
  rcases hlip with ⟨k, hk_pos, hk⟩
  unfold lipschitz at hk
  use ε / (2*k)
  constructor
  · calc
      ε / (2*k) = ε/2 * 1/k := by ring
      _ > 0 := by apply mul_pos (by linarith)
                  exact inv_pos_of_pos hk_pos
  intro x y hxy
  let df := d(f x, f y); let d := d(x, y)
  refold_let df d
  calc df ≤ k * d := by exact hk x y
        _ ≤ k * (ε/(2*k)) := by apply mul_le_mul_of_nonneg_left hxy
                                exact le_of_lt hk_pos
        _ = ε/2 := by field
        _ ≤ ε := by linarith

-- Définition 3.18.

variable {ι : Type} {Y : ι → Type}

def proj : (i : ι) → (Π i, Y i) → Y i := i ↦ x ↦ (x i)

@[simp] def prod_espaces (V : (i : ι) → Partie Y i) := ⋂ i, (proj i) ⁻¹' V i

lemma mem_prod_iff (x : (i : ι) → Y i) (V : (i : ι) → Partie Y i) :
  x ∈ prod_espaces V ↔ ∀ i, proj i x ∈ V i := by simp

lemma mem_prod_espaces (x : Π i, Y i) (V : (i : ι) → Partie Y i) :
  x ∈ prod_espaces V ↔ ∀ i, x i ∈ V i := by
  apply Iff.intro
  · intro h i; rw [prod_espaces, mem_iInter] at h; exact h i
  · intro h; rw [prod_espaces, mem_iInter]; intro i; exact h i

variable [∀ i, EspTop (Y i)]

def top_init {X : Type} (f : (i : ι) → X → Y i) : EspTop X := topo_engendree
  {A : Set X | ∃ i : ι, ∃ U : Partie (Y i), est_ouvert U ∧ A = (f i) ⁻¹' U}

instance top_prod : EspTop (Π i, Y i) := top_init (fun i ↦ x ↦ x i)

--instance top_prod_fini {n : ℕ} (Y : Fin n → Type) [∀ i, EspTop (Y i)] :
--  EspTop (Π i, Y i) := top_init (fun i ↦ x ↦ x i)

lemma ouvert_pref_projections {X : Type} (f : (i : ι) → X → Y i) (i : ι)
  (U : Set (Y i)) (hU : est_ouvert U) :
  @est_ouvert X (top_init f) ((f i) ⁻¹' U) := by
  apply ouv_top_engendree.ouvS
  dsimp; exact ⟨i, U, hU, rfl⟩

@[simp] def prod_ouverts (U : Partie (Π i, Y i)) (V : (i : ι) → Partie Y i) :=
  (∀ i, est_ouvert (V i)) ∧ U = prod_espaces V

def ouv_elementaire (u : Partie Π i, Y i) := ∃ V : (i : ι) → Partie Y i,
  prod_ouverts u V ∧ (∃ J : Set ι, Finite J ∧ ∀ i ∉ J, V i = Ω)

def transport_index {i j : ι} (h : i = j) (A : Partie Y i) : Partie Y j :=
  cast (by rw [h]) A
-- @Eq.rec Type (Partie Y i) (X ↦ _ ↦ X) A (Partie Y j) (by rw [h])

lemma ouv_elem_of_finite (u : Partie Π i, Y i) [Finite ι] (V : (i : ι) → Partie Y i)
  (hV : prod_ouverts u V) : ouv_elementaire u := by
  use V, hV; use Ω, finite_univ; intro i hi; absurd hi; apply mem_univ

open Classical in
lemma ouv_elem_of_preimage {i : ι} (A : Partie Y i) (h : est_ouvert A) :
  ouv_elementaire (proj i ⁻¹' A) := by
  let V := j ↦ dite (i = j) (h ↦ transport_index h A) (_ ↦ Ω)
  have transport_eq : V i = A := by
    unfold V; rw [dif_pos (refl i)]; rfl
  use V; apply And.intro
  · apply And.intro
    · intro j; by_cases eq : i = j
      · rwa [←eq, transport_eq]
      · unfold V; rw [dif_neg eq]; exact univ_ouvert
    · unfold prod_espaces V
      simp [apply_dite, iInter_dite]; congr
  · use {i}, Finite.of_subsingleton; intro j hj; unfold V
    rw [notMem_singleton_iff] at hj; symm at hj; rw [dif_neg hj]

lemma ouv_elem_of_univ : ouv_elementaire (Ω (α := Π i, Y i)) := by
  use j ↦ Ω, (by simp); use ∅, finite_empty
  intro i hi; rfl

lemma ouv_elem_of_inter {u v : Partie Π i, Y i} (h₁ : ouv_elementaire u)
  (h₂ : ouv_elementaire v) : ouv_elementaire (u ∩ v) := by
  rcases h₁ with ⟨U, ⟨U_ouv, hU⟩, ⟨J₁, J_fin₁, hJ₁⟩⟩
  rcases h₂ with ⟨V, ⟨V_ouv, hV⟩, ⟨J₂, J_fin₂, hJ₂⟩⟩
  use i ↦ U i ∩ V i; apply And.intro
  · dsimp; apply And.intro
    · intro i; exact inter_ouvert (U_ouv i) (V_ouv i)
    · rw [hU, hV]; simp [iInter_inter_distrib]
  · use J₁ ∪ J₂, Finite.union J_fin₁ J_fin₂
    intro i hi; rw [mem_union, not_or] at hi
    rw [hJ₁ i hi.1, hJ₂ i hi.2, inter_univ]

open Classical in
lemma ouv_elem_of_empty [ne : Nonempty ι] : ouv_elementaire (∅ : Set (Π i, Y i))
  := by
  let i := Nonempty.some ne
  let V : (j : ι) → Partie Y j := j ↦ ite (i = j) ∅ Ω
  use V; dsimp [V]; apply And.intro
  · apply And.intro
    · intro j; by_cases eq : i = j
      · rw [if_pos eq]; exact empty_ouvert
      · rw [if_neg eq]; exact univ_ouvert
    · simp [apply_ite, iInter_ite]
  · use {i}, Finite.of_subsingleton; intro j hj
    rw [notMem_singleton_iff] at hj; symm at hj; rw [if_neg hj]

lemma ouv_of_ouv_elem (U : Partie (Π i, Y i)) (h : ouv_elementaire U) :
  est_ouvert U := by
  rcases h with ⟨V, ⟨V_ouv, hV⟩, ⟨J, J_fin, hJ⟩⟩
  have eq : U = ⋂ i ∈ J, (proj i) ⁻¹' V i := by
    rw [hV, prod_espaces, ←biInter_univ, ←union_compl_self J]
    have eq_univ : ⋂ i ∈ Jᶜ, (proj i) ⁻¹' V i = Ω := by
      simp only [iInter_eq_univ]; intro i hi
      rw [hJ i hi, preimage_univ]
    rw [biInter_union, eq_univ, inter_univ]
  rw [eq]; apply inter_fini_ouvert; intro i hi
  apply ouvert_pref_projections; exact V_ouv i

theorem ouv_eq_elem_union (U : Partie (Π i, Y i)) (h : est_ouvert U) : ∃ V
  : Set (Set (Π i, Y i)), (∀ v ∈ V, ouv_elementaire v) ∧ U = ⋃₀ V := by
  induction h
  · case ouvS A hA =>
      rcases hA with ⟨i, V, V_ouv, hV⟩
      use {proj i ⁻¹' V}; apply And.intro
      · intro v hv; rw [hv]
        apply ouv_elem_of_preimage; exact V_ouv
      · rw [hV, sUnion_singleton]; rfl
  · case univS =>
      use {Ω}; apply And.intro
      · intro v hv; rw [hv]; exact ouv_elem_of_univ
      · rw [sUnion_singleton]
  · case emptyS => use ∅; simp
--
  · case unionS F _ hF =>
      have exists_i : ∀ i : F.ι, ∃ V, (∀ v ∈ V, ouv_elementaire v) ∧
        F.u i = ⋃₀ V := by intro i; apply hF; use i
      choose u h₁ h₂ using exists_i
      use ⋃ i, u i; apply And.intro
      · intro v ⟨V, ⟨i, hi⟩, hv⟩; dsimp at hi
        rw [←hi] at hv; exact h₁ i v hv
      · rw [sUnion_iUnion, Famille.iUnion]; congr; ext i x; rw [h₂]
--
  · case interS A B _ _ hA hB =>
      rcases hA with ⟨V₁, V₁_elem, hV₁⟩
      rcases hB with ⟨V₂, V₂_elem, hV₂⟩
      use {s ∩ t | (s ∈ V₁) (t ∈ V₂)}; apply And.intro
      · intro v ⟨s, hs, t, ht, hv⟩; rw [←hv]
        apply ouv_elem_of_inter (V₁_elem s hs) (V₂_elem t ht)
      · rw [hV₁, hV₂]; ext x; apply Iff.intro
        · intro ⟨⟨s, hs, in_s⟩, ⟨t, ht, in_t⟩⟩
          use s ∩ t, (by use s, hs, t, ht), in_s, in_t
        · intro ⟨v, ⟨s, hs, t, ht, hv⟩, x_in⟩;
          rw [←hv] at x_in; apply And.intro
          · use s, hs, x_in.left
          · use t, ht, x_in.right

-- Théorème 3.19.

-- a)

theorem vois_of_prod (X : Partie (Π i, Y i)) (x : Π i, Y i) : est_vois x X ↔
  ∃ U ⊆ X, ouv_elementaire U ∧ x ∈ U := by
  apply Iff.intro
  · intro h; rcases h with ⟨V, ⟨x_in, V_ouv, V_in⟩⟩
    rcases ouv_eq_elem_union V V_ouv with ⟨S, ⟨hS, union⟩⟩
    rw [union, mem_sUnion] at x_in; rcases x_in with ⟨v, v_in, x_in⟩
    have in_V : v ⊆ V := by
      rw [union]; exact subset_sUnion_of_mem v_in
    use v, subset_trans in_V V_in, hS v v_in
  · intro h; rcases h with ⟨U, U_in, U_ouv, x_in⟩
    use U, x_in, ouv_of_ouv_elem U U_ouv, U_in

-- b)

lemma est_vois_of_preimage_of_vois (x : Π i, Y i) {i : ι} {V : Partie Y i}
  (h : est_vois (x i) V) : est_vois x (proj i ⁻¹' V) := by
  rcases h with ⟨U, ⟨x_in, hU, U_in⟩⟩
  use proj i ⁻¹' U; constructor
  · exact x_in
  · apply ouvert_pref_projections; exact hU
  · intro x hx; exact U_in hx

theorem conv_vers_in_prod (u : ℕ → Π i, Y i) (l : Π i, Y i) : converge_vers u l ↔
  ∀ i, converge_vers (n ↦ (u n) i) (l i) := by
  apply Iff.intro
  · intro h i V hV; let U := proj i ⁻¹' V
    have hU := est_vois_of_preimage_of_vois l hV
    rcases h U hU with ⟨N, hN⟩; use N; intro m hm
    exact hN m hm
  · intro h V hV; rw [vois_of_prod] at hV
    rcases hV with ⟨U, U_in, ⟨W, ⟨W_ouv, hW⟩, ⟨J, J_fin, hJ⟩⟩, l_in⟩
    have vois_im : ∀ i, est_vois (l i) (W i) := by
      intro i; apply ouv_est_vois (W_ouv i)
      rw [hW, prod_espaces, mem_iInter] at l_in; exact l_in i
    choose! f hf using h; let g := i ↦ f i (W i)
--
    have exists_N : ∀ i, ∀ n ≥ g i, (u n) i ∈ W i := by
      intro i; exact hf i (W i) (vois_im i)
    have exists_max : ∃ N, ∀ i ∈ J, N ≥ g i := by
      suffices h : BddAbove {g i | i ∈ J} by
        rcases h with ⟨M, hM⟩; use M; intro i hi
        apply hM; use i, hi
      apply SupReal.bddabove_of_finite_image
    rcases exists_max with ⟨N, hN⟩; use N; intro n n_ge
--
    apply U_in; rw [hW, mem_prod_espaces]; intro i
    by_cases in_J : i ∈ J
    · case pos => apply exists_N; linarith [hN i in_J]
    · case neg => rw [hJ i in_J]; apply mem_univ

theorem converge_in_prod (u : ℕ → Π i, Y i) : converge u ↔ ∀ i, converge
  (n ↦ (u n) i) := by
  apply Iff.intro
  · intro ⟨l, hl⟩ i; use l i; rw [conv_vers_in_prod] at hl; exact hl i
  · intro h; choose l hl using h; use l; rwa [←conv_vers_in_prod] at hl

-- c)

theorem separe_of_prod_separe [S : ∀ i, EspSepareT2 (Y i)] : EspSepareT2 (Π i, Y i)
  := by
  constructor; intro x y h
  have exists_ne : ∃ i, x i ≠ y i := by
    contrapose h; push_neg at h; ext i; exact h i
  rcases exists_ne with ⟨i, hi⟩
  rcases (S i).est_separe (x i) (y i) hi with ⟨U, V, hU, hV, x_in, y_in, disj⟩
  let U' := (proj i) ⁻¹' U; let V' := (proj i) ⁻¹' V
  use U', V', ouvert_pref_projections proj i U hU,
      ouvert_pref_projections proj i V hV, x_in, y_in
  rw [eq_empty_iff_forall_notMem]; intro z z_in
  rw [←mem_empty_iff_false (z i), ←disj]; exact z_in

instance [∀ i, EspSepareT2 (Y i)] : EspSepareT2 (Π i, Y i) := separe_of_prod_separe

-- Exemple 3.21.

-- a)

omit [∀ i, EspTop (Y i)]

noncomputable def metrique_of_prod_metrique [M : ∀ i, EspaceMetrique (Y i)]
  [h : Nonempty ι] [Finite ι] : EspaceMetrique (Π i, Y i) := by
  let S (x y : (Π i, Y i)) : Set ℝ := {d(x i, y i) | i}
  have bdd_above (x y : (Π i, Y i)) : BddAbove {d(x i, y i) | i} := by
    apply SupReal.bddabove_of_finite_image'
  have bdd_below (x y : (Π i, Y i)) : BddBelow {d(x i, y i) | i} := by
    apply SupReal.bddbelow_of_finite_image'
  let d : (Π i, Y i) → (Π i, Y i) → ℝ := x ↦ y ↦ sSup {d(x i, y i) | i}
--
  use d; rcases h with ⟨i⟩; constructor
  · intro x y; apply le_csSup_of_le (b := d(x i, y i))
    · exact bdd_above x y
    · use i
    · apply (M i).is_dist.nneg
--
  · intro x y; apply Iff.intro
    · intro eq; ext i; rw [←(M i).is_dist.sep]
      apply le_antisymm _ ((M i).is_dist.nneg (x i) (y i))
      rw [←eq]; apply le_csSup (bdd_above x y); use i
    · intro eq; apply SupReal.sSup_const
      · use d(x i, y i); use i
      · intro d ⟨i, hi⟩; rw [←hi, (M i).is_dist.sep, eq]
--
  · intro x y; unfold d; congr 1; ext d; apply Iff.intro
    · intro ⟨i, hi⟩; use i; rw [←hi, (M i).is_dist.symm]
    · intro ⟨i, hi⟩; use i; rw [←hi, (M i).is_dist.symm]
--
  · intro x y z; have bdd_add :=
      SupReal.add_bddabove (bdd_above x y) (bdd_above y z)
    apply le_trans (b := sSup (S x y + S y z)) _
    · apply SupReal.sSup_add_ineq _ (bdd_above x y) _ (bdd_above y z)
      · use d(x i, y i); use i
      · use d(y i, z i); use i
    · unfold d; apply csSup_le
      · use d(x i, z i); use i
      · intro d₁ ⟨i, hi⟩
        apply le_csSup_of_le (b := d(x i, y i) + d(y i, z i)) bdd_add
        · use ⟨d(x i, y i), d(y i, z i)⟩; apply And.intro
          · use (by use i); use i
          · ring
        · rw [←hi]; apply (M i).is_dist.ineq

noncomputable instance instProd [∀ i, EspaceMetrique (Y i)] [h : Nonempty ι]
  [Finite ι] : EspaceMetrique (Π i, Y i) := metrique_of_prod_metrique

lemma prod_dist [∀ i, EspaceMetrique (Y i)] [h : Nonempty ι] [Finite ι] (x y :
  Π i, Y i) : d(x, y) = sSup {d(x i, y i) | i} := by rfl

lemma le_prod_dist [∀ i, EspaceMetrique (Y i)] [h : Nonempty ι] [Finite ι]
  (x y : Π i, Y i) : ∀ i, d(x i, y i) ≤ d(x, y) := by
  intro i; rw [prod_dist]; apply le_csSup _ (by use i)
  apply SupReal.bddabove_of_finite_image'

noncomputable instance instProdFin {n : ℕ} {h : n > 0} {F : Fin n → Type} [∀ i,
  EspaceMetrique (F i)] : EspaceMetrique (Π i, F i) := by
  have ne : Nonempty (Fin n) := by use 0
  apply metrique_of_prod_metrique

variable [∀ i, EspaceMetrique (Y i)] [nempty : Nonempty ι] [Finite ι]

lemma ouv_elem_of_boule (a : Π i, Y i) (r : ℝ) : @ouv_elementaire _ _ (_ ↦ ofMet)
  (Bₒ a r) := by
  apply ouv_elem_of_finite (V := i ↦ Bₒ (a i) r)
  dsimp; apply And.intro
  · intro i; exact ouv_of_boule_ouv (a i) r
  · ext x; apply Iff.intro
    · intro h; rw [mem_iInter]; intro i; dsimp
      exact lt_of_le_of_lt (le_prod_dist x a i) h
    · intro h; dsimp; rw [prod_dist, Finite.csSup_lt_iff]
      · intro z ⟨i, hi⟩; rw [←hi]; rw [mem_iInter] at h; exact h i
      · apply SupReal.image_of_fin
      · let i := Nonempty.some nempty; use d(x i, a i); use i

lemma ouv_of_metrique_iff_ouv_of_top_prod : ∀ s : Partie Π i, Y i, ofMet.est_ouvert s
  ↔ (@top_prod _ _ (_ ↦ ofMet)).est_ouvert s := by
  intro s; apply Iff.intro
  · intro h; rw [ouvert_ssi_vois]; intro x hx
    rw [vois_of_prod]; rcases h x hx with ⟨r, r_pos, hr⟩
    use Bₒ x r, hr, ouv_elem_of_boule x r, centre_in_boule x r_pos
--
  · intro h a ha; rw [ouvert_ssi_vois] at h
    specialize h a ha; rw [vois_of_prod] at h
    rcases h with ⟨U, U_in, ⟨p, ⟨p_ouv, hp⟩, _⟩, a_in⟩
    rw [hp, mem_prod_iff] at a_in
    have exists_r : ∀ i, ∃ r > 0, Bₒ (a i) r ⊆ p i := by
      intro i; apply p_ouv i; exact a_in i
    choose f hf₁ hf₂ using exists_r; let S := Set.range f
--
    let i := Nonempty.some nempty
    have hn : S.Nonempty := by use (f i); use i
    have hf : Finite S := by apply SupReal.image_of_fin
    use sInf S; apply And.intro
    · rw [gt_iff_lt, Finite.lt_csInf_iff hf hn]
      intro x ⟨j, hj⟩; rw [←hj]; exact hf₁ j
    · intro x hx; apply U_in; rw [hp, mem_prod_iff]
      intro j; apply hf₂; dsimp; apply lt_of_le_of_lt
      · exact le_prod_dist x a j
      · apply lt_of_lt_of_le hx; apply csInf_le _ (by use j)
        apply SupReal.bddbelow_of_finite_image'

lemma vois_of_metrique_iff_vois_of_top (x : Π i, Y i) (X : Partie Π i, Y i) :
  ofMet.est_vois x X ↔ (@top_prod _ _ (_ ↦ ofMet)).est_vois x X := by
  apply Iff.intro
  · intro h; rcases h with ⟨U, ⟨x_in, hU, U_in⟩⟩
    rw [ouv_of_metrique_iff_ouv_of_top_prod] at hU
    use U, x_in, hU, U_in
  · intro h; rcases h with ⟨U, ⟨x_in, hU, U_in⟩⟩
    rw [←ouv_of_metrique_iff_ouv_of_top_prod] at hU
    use U, x_in, hU, U_in

lemma conv_vers_metrique_iff_conv_vers_top (u : ℕ → Π i, Y i) (l : Π i, Y i) :
  ofMet.converge_vers u l ↔ (@top_prod _ _ (_ ↦ ofMet)).converge_vers u l := by
  apply Iff.intro
  · intro h U hU; rw [←vois_of_metrique_iff_vois_of_top] at hU
    rcases h U hU with ⟨n, hn⟩; use n, hn
  · intro h U hU; rw [vois_of_metrique_iff_vois_of_top] at hU
    rcases h U hU with ⟨n, hn⟩; use n, hn

theorem conv_to_in_prod (u : ℕ → Π i, Y i) (l : Π i, Y i) : converges_to u l ↔ ∀ i,
  converges_to (n ↦ (u n) i) (l i) := by
  apply Iff.intro
  · unfold converges_to at *; intro conv_l i; intro ε ε_pos ; specialize conv_l ε ε_pos; rcases conv_l with ⟨N, hN⟩;
    use N; intro n hn; specialize hN n hn;
    calc
      d((fun n ↦ u n i) n,  (l i)) ≤ d((u n), l) := by apply le_prod_dist (u n) l
      _ ≤ ε := hN
  · expose_names; intro h ε ε_pos; have h_chaque : ∀ (i : ι), ∃ N, ∀ n ≥ N, d((fun n ↦ u n i) n, (l i)) ≤ ε := by
                                    intro i
                                    specialize h i
                                    exact h ε ε_pos
    choose N hN using h_chaque
    let rang_N : Finset ℕ :=  Finset.image N ι

    --simp only [←conv_vers_iff_conv_to] at *
    --simp only [conv_vers_metrique_iff_conv_vers_top]
    --rwa [←conv_vers_in_prod] at h

theorem converges_in_prod (u : ℕ → Π i, Y i) : converges u ↔ ∀ i, converges
  (n ↦ (u n) i) := by
  apply Iff.intro
  · intro ⟨l, hl⟩ i; use l i; rw [conv_to_in_prod] at hl; exact hl i
  · intro h; choose l hl using h; use l; rwa [←conv_to_in_prod] at hl

--def est_ouvert_elementaire (s : Set (X × X)) :=
--  ∃ U1 U2 : Set X, (s = (U1 × U2)) ∧ (est_ouvert U1) ∧ (est_ouvert U2)

--instance top_prod {ι : Type}{u : ι → Set (X × X)} : EspTop (X × X) where
--  est_ouvert := fun w ↦ (w = ⋂ i, u i) ∧ (∀ i, est_ouvert_elementaire (u i))
--  univ_ouvert :=

-- Proposition 3.23.

abbrev X_square (X : Type) [EspTop X] := Π _ : Fin 2, X
notation : max X "²" => X_square X

abbrev p1 (x : X²) : X := x (0 : Fin 2)
abbrev p2 (x : X²) : X := x (1 : Fin 2)

def diagonale (X : Type) [EspTop X] : Partie X² := {x | p1 x = p2 x}
notation : max "Δ" X : max => diagonale X

def prod_in_square (U V : Partie X) : Partie X² := {x | p1 x ∈ U ∧ p2 x ∈ V}
notation U : max " ×₂ " V : max => prod_in_square U V

def prod_fun (U V : Partie X) : Fin 2 → Partie X := n ↦ match n with
  | 0 => U
  | 1 => V
notation U : max " ×² " V : max => prod_fun U V

lemma prod_eq_prod₂ (U V : Partie X) : U ×₂ V = prod_espaces (U ×² V) := by
  unfold prod_fun prod_in_square prod_espaces; ext x
  rw [mem_iInter, Fin.forall_fin_two]; rfl

lemma prod₂_eq_prod (p : Fin 2 → Partie X) : prod_espaces p = (p 0) ×₂ (p 1) := by
  suffices h : p = (p 0) ×² (p 1) by nth_rw 1 [h, ←prod_eq_prod₂]
  apply funext; rw [Fin.forall_fin_two]; apply And.intro; repeat rfl

def prod_elem (x y : X) : X² := n ↦ match n with
  | 0 => x
  | 1 => y
notation "{" x " , " y "}₂" => prod_elem x y

lemma not_mem_diagonale (x : X²) : x ∉ Δ X ↔ p1 x ≠ p2 x := by rfl
lemma mem_compl_diagonale (x : X²) : x ∈ (Δ X)ᶜ ↔ p1 x ≠ p2 x := by rfl

lemma subset_compl_diagonale (U V : Partie X) : (U ×₂ V) ⊆ (Δ X)ᶜ ↔
  U ∩ V = ∅ := by
  apply Iff.intro
  · intro h; rw [eq_empty_iff_forall_notMem]
    intro x hx; have x_in : {x, x}₂ ∈ Δ X := by rfl
    apply h _ x_in; exact ⟨hx.1, hx.2⟩
  · intro h x x_in; rw [mem_compl_diagonale]
    intro eq; rw [←mem_empty_iff_false (p1 x), ←h]
    apply And.intro x_in.1; rw [eq]; exact x_in.2

theorem separe_iff_diag_ferme : EspSepareT2 X ↔ est_ferme Δ X := by
  apply Iff.intro
  · intro ⟨h⟩; rw [est_ferme, ouvert_ssi_vois]
    intro x hx; rw [mem_compl_diagonale] at hx
    rcases h (p1 x) (p2 x) hx with ⟨U, V, hU, hV, p1_in, p2_in, disj⟩
    rw [vois_of_prod]; use U ×₂ V; apply And.intro
    · rwa [subset_compl_diagonale]
    · apply And.intro _ ⟨p1_in, p2_in⟩; use U ×² V
      apply And.intro
      · apply And.intro _ (prod_eq_prod₂ U V)
        rw [Fin.forall_fin_two]; exact ⟨hU, hV⟩
      · use Ω, finite_univ; intro i hi; absurd hi; apply mem_univ
--
  · intro h; rw [est_ferme, ouvert_ssi_vois] at h
    constructor; intro x y hyp
    simp only [mem_compl_diagonale, vois_of_prod] at h
    rcases h {x, y}₂ hyp with ⟨U, U_in, ⟨p, hp, _⟩, in_U⟩
    rcases hp with ⟨h₁, h₂⟩; use p 0, p 1, h₁ 0, h₁ 1
    rw [h₂, mem_prod_iff, Fin.forall_fin_two] at in_U
    apply And.intro in_U.1; apply And.intro in_U.2
    rwa [h₂, prod₂_eq_prod, subset_compl_diagonale] at U_in
