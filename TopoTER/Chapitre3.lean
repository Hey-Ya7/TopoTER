import TopoTER.Chapitre2

open TER Set EspTop Metrique

variable {X Y Z : Type} [EspTop X] [EspTop Y] [EspTop Z] [EspSepareT2 Y]
variable {E F : Type} [M : EspaceMetrique E] [EspaceMetrique F]

def est_continu_point {X Y : Type} [EspTop X] [EspTop Y] (f : X → Y) (x : X) : Prop :=
  ∀(V : Set Y), (est_vois (f x) V) → ∃(U : Set X), (est_vois x U) ∧  (f '' U ⊆ V)

def est_continu {X Y : Type} [EspTop X] [EspTop Y] (f : X → Y) : Prop :=
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
  intro x y; unfold instEspaceMetriqueReal
  dsimp; rw [one_mul, abs_sub_le_iff];
  apply And.intro
  · apply sub_ineq V.is_norm
  · unfold instEspaceMetriqueEspaceMetNorme; dsimp
    rw [norm_symm V.is_norm]; apply sub_ineq V.is_norm

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

variable {ι : Type} {Y : ι → Type} [∀ i, EspTop (Y i)]

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

def proj : (i : ι) → (Π i, Y i) → Y i := i ↦ x ↦ (x i)

def prod_espaces (V : (i : ι) → Partie Y i) := ⋂ i, (proj i) ⁻¹' V i

omit [(i : ι) → EspTop (Y i)] in
lemma mem_prod_espaces (x : Π i, Y i) (V : (i : ι) → Partie Y i) :
  x ∈ prod_espaces V ↔ ∀ i, x i ∈ V i := by
  apply Iff.intro
  · intro h i; rw [prod_espaces, mem_iInter] at h; exact h i
  · intro h; rw [prod_espaces, mem_iInter]; intro i; exact h i

def prod_ouverts (U : Partie (Π i, Y i)) (V : (i : ι) → Partie Y i) :=
  (∀ i, est_ouvert (V i)) ∧ U = prod_espaces V

def ouv_elementaire (U : Partie (Π i, Y i)) := ∃ V : (i : ι) → Partie Y i,
  prod_ouverts U V ∧ (∃ J : Set ι, Finite J ∧ ∀ i ∉ J, V i = Ω)

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

-- Théorème 3.19.

-- a)

theorem vois_of_prod (X : Partie (Π i, Y i)) (x : Π i, Y i) : est_vois x X ↔
  ∃ U ⊆ X, ouv_elementaire U ∧ x ∈ U := by
  apply Iff.intro
  · intro h; rcases h with ⟨V, ⟨x_in, V_ouv, V_in⟩⟩
    sorry
  · intro h; rcases h with ⟨U, U_in, U_ouv, x_in⟩
    use U; constructor
    · exact x_in
    · exact ouv_of_ouv_elem U U_ouv
    · exact U_in

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

--def est_ouvert_elementaire (s : Set (X × X)) :=
--  ∃ U1 U2 : Set X, (s = (U1 × U2)) ∧ (est_ouvert U1) ∧ (est_ouvert U2)

--instance top_prod {ι : Type}{u : ι → Set (X × X)} : EspTop (X × X) where
--  est_ouvert := fun w ↦ (w = ⋂ i, u i) ∧ (∀ i, est_ouvert_elementaire (u i))
--  univ_ouvert :=
