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

lemma comp_est_continu {X Y Z : Type}  [EspTop X] [EspTop Y] [EspTop Z] (f : X → Y) (g : Y → Z) (hf : est_continu f) (hg : est_continu g) :
  est_continu (g ∘ f) := by
    rw[continu_iff_preim_ouv] at *
    intro V hV
    rw[Set.preimage_comp]
    apply hf
    apply hg
    exact hV

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



def top_init {X ι : Type} {Y : ι → Type} [∀ i, EspTop (Y i)] (f : (i : ι) → X → Y i) : EspTop X :=
  topo_engendree {A : Set X | ∃ i : ι, ∃ U : Partie (Y i), est_ouvert U ∧ A = (f i) ⁻¹' U}

instance top_prod {ι : Type} (Y : ι → Type) [∀ i, EspTop (Y i)] : EspTop (Π i, Y i) :=
  top_init (fun i ↦ x ↦ x i)

instance top_prod_fini {n : ℕ} (Y : Fin n → Type) [∀ i, EspTop (Y i)] : EspTop (Π i, Y i) :=
  top_init (fun i ↦ x ↦ x i)


lemma ouvert_pref_projections {X ι : Type} {Y : ι → Type} [∀ i, EspTop (Y i)]
  (f : (i : ι) → X → Y i) (i : ι) (U : Set (Y i)) (hU : est_ouvert U) :
  @est_ouvert X (top_init f) ((f i) ⁻¹' U) := by
  apply ouv_top_engendree.ouvS
  dsimp
  exact ⟨i, U, hU, rfl⟩

lemma vois_pref_projections {X ι : Type} {Y : ι → Type} [∀ i, EspTop (Y i)]
  (f : (i : ι) → X → Y i) (i : ι) (x : X) (V : Set (Y i)) (hV : est_vois (f i x) V) :
  @est_vois X (top_init f) x ((f i) ⁻¹' V) := by
  letI tX : EspTop X := top_init f
  -- 1. On extrait l'ouvert témoin U du voisinage V dans l'espace Y i
  rcases hV with ⟨U, hU⟩

  -- 2. On pose que l'ouvert témoin dans X sera l'image réciproque (f i) ⁻¹' U
  let U_X := (f i) ⁻¹' U
  use U_X
  exact ⟨hU.x_dans, ouvert_pref_projections f i U hU.ouv_ouvert , by intro y hy
                                                                     have hU_V : f i ⁻¹' U ⊆ f i ⁻¹' V := by
                                                                      intro z hz
                                                                      rw[Set.mem_preimage] at *
                                                                      have U_in_V : U ⊆ V :=
                                                                        hU.ouv_contenu
                                                                      exact U_in_V hz
                                                                     exact hU_V hy
                                                                     ⟩

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

--lemma voisinage_produit_fini {X : Type} [EspTop X] (H : Set (Fin 2 → X)) (hH : est_ouvert H) (f : Fin 2 → X) (hf : f ∈ H) :
--  ∃ (U V : Set X), est_ouvert U ∧ est_ouvert V ∧ f 0 ∈ U ∧ f 1 ∈ V ∧ {g | g 0 ∈ U} ∩ {g | g 1 ∈ V} ⊆ H := by
--    change ouv_top_engendree _ H at hH




lemma sep_iff_diag_ferme {X : Type} [EspTop X] :
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
      refine { est_separe := by sorry
                              --intro x y hxy;
                              --rw[est_ferme, h, ouvert_ssi_vois] at hFerme
                              --let proj : Fin 2 → X := fun | 0 => x | 1 => y
                              --have proj_in_ferme : proj ∈ {f | f 0 ≠ f 1} := by
                              --  exact mem_setOf.mpr hxy
                              --specialize hFerme proj proj_in_ferme
                              --rcases hFerme with ⟨H, ⟨hprojH, houvH, hHin⟩⟩
                              --rw[est_ouvert] at houvH


              }


lemma prop_uni_continu {X ι : Type} {Y : ι → Type} [EspTop X] [∀ i, EspTop (Y i)] (f : X → Π i, Y i) : est_continu f ↔ ∀ i : ι, est_continu ((fun y ↦ y i) ∘ f) := by
  constructor
  · intro hfcont i
    apply comp_est_continu
    · exact hfcont
    · rw[continu_iff_preim_ouv]
      intro V hV
      apply ouvert_pref_projections
      exact hV
  · intro h
    rw [continu_iff_preim_ouv]
    intro V hV
    induction hV with
    | ouvS U hU =>
        rcases hU with ⟨i, O, hO, rfl⟩
        rw [← Set.preimage_comp]
        have hc := h i
        rw [continu_iff_preim_ouv] at hc
        exact hc O hO
    | univS =>
        rw [preimage_univ]
        exact univ_ouvert
    | emptyS =>
        rw [preimage_empty]
        exact empty_ouvert
    | unionS hU ih =>
        expose_names
        sorry
        --rw[preimage_iUnion]
    | interS hU hV ihU ihV =>
        rw [preimage_inter]
        exact inter_ouvert ihU ihV



lemma fun_eq_dense (f g : X → Y) {A : Partie X} (hA : dense X A) (hf : est_continu f)
(hg : est_continu g) (hfg : A.restrict f = A.restrict g)
 : f = g := by
  let Efg : Partie X := {x : X | f x = g x}
  have hAinEfg : A ⊆ Efg:= by
    intro x hx
    rw[mem_setOf]
    rw[restrict_def] at hfg
    have h_val := congr_fun hfg ⟨x, hx⟩
    exact h_val
  have Efg_ferme : est_ferme Efg := by
    let proj : X → Fin 2 → Y := x ↦ fun | 0 => f x
                                        | 1 => g x
    have proj_cont : est_continu proj := by
      rw[prop_uni_continu]
      intro i
      fin_cases i
      · change est_continu f
        exact hf
      · change est_continu g
        exact hg
    rw[continu_iff_preim_ferm] at proj_cont
    have diag_f : est_ferme {f : Fin 2 → Y | f 0 = f 1} := by
      (expose_names; exact sep_iff_diag_ferme.mp inst_2)
    specialize proj_cont ({f | f 0 = f 1}) (diag_f)
    have eq_preimage_diag : proj ⁻¹' {f | f 0 = f 1} = Efg := preimage_setOf_eq
    rwa [eq_preimage_diag] at proj_cont
  have adh_A_in_adh_E : adh A ⊆ adh Efg := adh_contenu_adh A Efg hAinEfg
  rw[hA] at adh_A_in_adh_E
  rw[ferme_iff_adh] at Efg_ferme
  rw[Efg_ferme] at adh_A_in_adh_E
  have Efg_eq_univ : Efg = univ := Eq.symm (Subset.antisymm adh_A_in_adh_E fun ⦃a⦄ a_1 ↦ trivial)
  exact (eqOn_univ f g).mp adh_A_in_adh_E













 --def est_ouvert_elementaire (s : Set (X × X)) :=
--  ∃ U1 U2 : Set X, (s = (U1 × U2)) ∧ (est_ouvert U1) ∧ (est_ouvert U2)

--instance top_prod {ι : Type}{u : ι → Set (X × X)} : EspTop (X × X) where
--  est_ouvert := fun w ↦ (w = ⋂ i, u i) ∧ (∀ i, est_ouvert_elementaire (u i))
--  univ_ouvert :=
