import TopoTER.Chapitre2

open TER Set EspTop Metrique

variable {X Y Z : Type} [T₁ : EspTop X] [T₂ : EspTop Y] [T₃ : EspTop Z]
variable {E F : Type} [M : EspaceMetrique E] [M' : EspaceMetrique F]

def est_continu_point (f : X → Y) (x : X) : Prop := ∀ (V : Set Y), est_vois (f x) V →
   ∃ U : Set X, est_vois x U ∧ f '' U ⊆ V

def est_continu (f : X → Y) : Prop := ∀ x, est_continu_point f x

def est_fun_ouverte (f : X → Y) : Prop := ∀ s, est_ouvert s → est_ouvert (f '' s)

lemma continu_of_id : est_continu (id (α := X)) := by
  intro x V hV; use V, hV; rw [image_id]

-- lemme fondamental pour la topologie induite:

def ofVal {A : Partie X} : Induite A → X := x ↦ x.val

open Set.Notation in
theorem continu_of_val {A : Partie X} : est_continu (ofVal (A := A)) := by
  intro x V ⟨U, ⟨x_in, U_ouv, hU⟩⟩; use A ↓∩ U
  apply And.intro
  · have x_in_U : x ∈ A ↓∩ U := by exact x_in
    apply ouv_est_vois _ x_in_U; use U
  · apply subset_trans _ hU
    apply image_val_preimage_val_subset_self

lemma vois_preim_of_continu {x : X} {f : X → Y} (hf : est_continu_point f x) {V : Partie Y}
  (hV : est_vois (f x) V) : est_vois x (f ⁻¹' V) := by
  rcases hf V hV with ⟨v, hv, v_in⟩; apply vois_trans hv
  rwa [image_subset_iff] at v_in

lemma continu_iff_preim_vois (f : X → Y) : est_continu f ↔ ∀ (V : Set Y),
  ∀ x, est_vois (f x) V → est_vois x (f ⁻¹' V) := by
  apply Iff.intro
  · intro h V x vois; exact vois_preim_of_continu (h x) vois
  · intro h x V vois; rcases h V x vois with ⟨u, x_in, hu, u_in⟩
    use u, ouv_est_vois hu x_in; rwa [image_subset_iff]

theorem continu_iff_preim_ouv (f : X → Z) : est_continu f ↔ ∀ (V : Set Z),
  est_ouvert V → est_ouvert (f ⁻¹' V) := by
  constructor
  · intro h V Vouv; rw [ouvert_ssi_vois]
    intro x hx; apply vois_preim_of_continu (h x)
    exact ouv_est_vois Vouv hx
  · rw [continu_iff_preim_vois]; intro h V x vois
    rcases vois with ⟨u, x_in, hu, u_in⟩
    use f ⁻¹' u, x_in, h u hu; intro x' hx'; exact u_in hx'

lemma ouv_preim_of_continu {f : X → Y} (hf : est_continu f) {U : Partie Y}
  (hu : est_ouvert U) : est_ouvert (f ⁻¹' U) := by
  rw [continu_iff_preim_ouv] at hf; exact hf U hu

lemma comp_est_continu {f : X → Y} {g : Y → Z} (hf : est_continu f) (hg : est_continu g) :
  est_continu (g ∘ f) := by
  rw [continu_iff_preim_ouv] at *
  intro V hV; rw [Set.preimage_comp]
  apply hf; apply hg; exact hV

theorem continu_iff_val_continu {A : Partie Y} (f : X → Induite A) : est_continu f ↔
  est_continu (ofVal ∘ f) := by
  apply Iff.intro
  · intro h; apply comp_est_continu h; exact continu_of_val
  · intro h; rw [continu_iff_preim_ouv]
    intro V ⟨U, U_ouv, hU⟩; rw [hU, ←preimage_comp]
    exact ouv_preim_of_continu h U_ouv

lemma continu_ouv_ferm (f : X → Y) : (∀ (V : Set Y), (est_ouvert V →
  est_ouvert (f ⁻¹' V))) ↔ (∀ (F : Set Y), est_ferme F → est_ferme (f ⁻¹' F)) := by
  constructor
  · intro h V hV
    specialize h Vᶜ hV
    rw [preimage_compl] at h
    exact h
  · intro h V hV
    rw [est_ouvert_iff_compl_est_ferme] at *
    specialize h Vᶜ hV
    rw[preimage_compl] at h
    exact h

theorem continu_iff_preim_ferm (f : X → Y) : est_continu f ↔ ∀ (F : Set Y),
  est_ferme F → est_ferme (f ⁻¹' F) := by
  rw[continu_iff_preim_ouv]
  exact continu_ouv_ferm f

lemma ferm_preim_of_continu {f : X → Y} (hf : est_continu f) {V : Partie Y}
  (hv : est_ferme V) : est_ferme (f ⁻¹' V) := by
  rw [continu_iff_preim_ferm] at hf; exact hf V hv

-- 3.2. Continuité dans un espace métrique

-- Proposition 3.10.

lemma image_conv_of_continu {f : X → Y} {l : X} (hf : est_continu_point f l) {u : ℕ → X}
  (hu : converge_vers u l) : converge_vers (f ∘ u) (f l) := by
  intro t ht; have h := vois_preim_of_continu hf ht
  rcases hu _ h with ⟨n, hn⟩; use n, hn

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

-- Définition 3.7.

class Homeomorphisme (f : X → Y) where
  inv : Y → X
  left_inv : inv ∘ f = id
  right_inv : f ∘ inv = id
  continu : est_continu f
  inv_continu : est_continu inv

class Homeomorphe (X Y : Type) [T₁ : EspTop X] [T₂ : EspTop Y] where
  homeo : X → Y
  est_homeo : Homeomorphisme homeo

instance homeo_refl (X : Type) [T : EspTop X] : Homeomorphe X X where
  homeo := id
  est_homeo := {
    inv := id
    left_inv := by rfl
    right_inv := by rfl
    continu := continu_of_id
    inv_continu := continu_of_id
  }

instance homeo_symm (X Y : Type) [T₁ : EspTop X] [T₂ : EspTop Y] [H : Homeomorphe X Y] :
  Homeomorphe Y X where
  homeo := H.est_homeo.inv
  est_homeo := {
    inv := H.homeo
    left_inv := H.est_homeo.right_inv
    right_inv := H.est_homeo.left_inv
    continu := H.est_homeo.inv_continu
    inv_continu := H.est_homeo.continu
  }

open Function
lemma left_inverse_of_homeo_inv {f : X → Y} [H : Homeomorphisme f] : LeftInverse H.inv f
  := by intro x; rw [←comp_apply (f := H.inv), H.left_inv]; rfl

lemma right_inverse_of_homeo_inv {f : X → Y} [H : Homeomorphisme f] : RightInverse H.inv f
  := by intro x; rw [←comp_apply (f := f), H.right_inv]; rfl

lemma injective_of_homeo {f : X → Y} [H : Homeomorphisme f] : Injective f := by
  by_cases h : Nonempty X
  · rw [injective_iff_hasLeftInverse]; use H.inv
    exact left_inverse_of_homeo_inv
  · rw [not_nonempty_iff] at h
    have empty : IsEmpty Y := by
      by_contra contra; rw [not_isEmpty_iff] at contra
      apply IsEmpty.elim' _ H.inv; rw [isEmpty_fun]
      exact ⟨contra, h⟩
    apply injective_of_subsingleton

lemma surjective_of_homeo {f : X → Y} [H : Homeomorphisme f] : Surjective f := by
  rw [surjective_iff_hasRightInverse]; use H.inv
  exact right_inverse_of_homeo_inv

lemma bijective_of_homeo {f : X → Y} [H : Homeomorphisme f] : Bijective f := by
  exact ⟨injective_of_homeo, surjective_of_homeo⟩

lemma ouv_iff_homeo_ouv {f : X → Y} [H : Homeomorphisme f] : ∀ s, est_ouvert s ↔
  est_ouvert (f '' s) := by
  let f' := H.inv; let hc := H.continu; let hc' := H.inv_continu
  intro s; apply Iff.intro
  · intro h; rw [continu_iff_preim_ouv] at hc'
    rw [image_eq_preimage_of_inverse (f := f) (g := f')]
    · exact hc' s h
    · exact left_inverse_of_homeo_inv (H := H)
    · exact right_inverse_of_homeo_inv (H := H)
  · intro h; rw [continu_iff_preim_ouv] at hc
    rw [←preimage_image_eq s (f := f) injective_of_homeo]; exact hc _ h

lemma ferme_iff_homeo_ferme {f : X → Y} [H : Homeomorphisme f] : ∀ s, est_ferme s ↔
  est_ferme (f '' s) := by
  intro s; unfold est_ferme; rw [ouv_iff_homeo_ouv (H := H)]
  rw [image_compl_eq]; exact bijective_of_homeo

noncomputable instance of_ouv_iff_ouv (f : X → Y) (hf : Bijective f) (h : ∀ s,
  est_ouvert s ↔ est_ouvert (f '' s)) : Homeomorphe X Y where
  homeo := f
  est_homeo := {
    inv := invBij hf
    left_inv := invBij_comp hf
    right_inv := comp_invBij hf
    continu := by {
      rw [continu_iff_preim_ouv]; intro s hs
      rwa [h, hf.surjective.image_preimage]
    }
    inv_continu := by {
      rw [continu_iff_preim_ouv]; intro s hs
      rw [←(hf.injective).preimage_image (s := s)]
      rwa [←preimage_comp, comp_invBij hf, preimage_id, ←h]
    }
  }

lemma vois_iff_homeo_vois [Homeo : Homeomorphe X Y] (x : X) (s : Set X) : est_vois x s ↔
  est_vois (Homeo.homeo x) (Homeo.homeo '' s) := by
  let f := Homeo.homeo; let H := Homeo.est_homeo
  let hc := H.continu; apply Iff.intro
  · intro h; rcases h with ⟨u, ⟨x_in, hu, u_in⟩⟩
    use (f '' u); constructor
    · use x
    · rwa [←ouv_iff_homeo_ouv]
    · rw [image_subset_iff]; apply subset_trans u_in
      apply subset_preimage_image
  · intro h; have inj := injective_of_homeo (H := H)
    rw [←preimage_image_eq s inj]; exact vois_preim_of_continu (hc x) h

lemma conv_iff_homeo_conv [Homeo : Homeomorphe X Y] (u : ℕ → X) (l : X) : converge_vers u l
  ↔ converge_vers (Homeo.homeo ∘ u) (Homeo.homeo l) := by
  let f := Homeo.homeo; let H := Homeo.est_homeo
  let f' := H.inv; let hc := H.continu; let hc' := H.inv_continu
  apply Iff.intro
  · intro h; exact image_conv_of_continu (hc l) h
  · intro h; rw [←id_comp u, ←id_def l, ←H.left_inv]
    exact image_conv_of_continu (hc' (f l)) h

lemma sep_iff_homeo_sep [Homeo : Homeomorphe X Y] [S : EspSepareT2 X] : EspSepareT2 Y := by
  let f := Homeo.homeo; let H := Homeo.est_homeo
  let f' := H.inv; let hinj := injective_of_homeo (H := H)
  constructor; intro x y hxy
  have hf'xy : f' x ≠ f' y := by
    intro eq; apply hxy
    rw [←id_def x, ←id_def y, ←H.right_inv]
    rw [comp_apply, comp_apply]; congr
  rcases S.est_separe (f' x) (f' y) hf'xy with ⟨U, V, hU, hV, f'x_in, f'y_in, disj⟩
  use (f '' U), (f '' V), (by rwa [←ouv_iff_homeo_ouv]), (by rwa [←ouv_iff_homeo_ouv]),
      (by rw [←id_def x, ←H.right_inv, comp_apply]; use f' x),
      (by rw [←id_def y, ←H.right_inv, comp_apply]; use f' y)
  rw [←image_inter_on (x ↦ y ↦ _ ↦ _ ↦ h ↦ hinj h), disj]; exact image_empty f

noncomputable instance homeo_met_ind {X : Type} [M : EspaceMetrique X] (A : Partie X) :
  Homeomorphe (Induite A) (MetInduite A) := of_ouv_iff_ouv id bijective_id
  (by intro s; rw [image_id, ouv_of_ind_iff_ouv_of_met]; rfl)

instance ind_homeo_ind {f : X → Y} [H : Homeomorphisme f] (A : Partie X) :
  Homeomorphe (Induite A) (Induite (f '' A)) where
  homeo := x ↦ ⟨f x, by use x, x.prop⟩
  est_homeo := {
    inv := y ↦ ⟨H.inv y, by {
      rcases y.prop with ⟨x, x_in, hx⟩; rw [←hx]
      rwa [←comp_apply (f := H.inv), H.left_inv]
    }⟩

    left_inv := by {
      ext x; dsimp; rw [←comp_apply (f := H.inv), H.left_inv]; rfl
    }
    right_inv := by {
      ext x; dsimp; rw [←comp_apply (f := f), H.right_inv]; rfl
    }

    continu := by {
      rw [continu_iff_val_continu]
      let F : Induite A → Induite (f '' A)
            := x ↦ ⟨f x, by use x, x.prop⟩
      let F' := ofVal ∘ F; refold_let F'
      have eq : F' = f ∘ ofVal := rfl
      rw [eq]; apply comp_est_continu continu_of_val
      exact H.continu
    }

    inv_continu := by {
      rw [continu_iff_val_continu]
      let G : Induite (f '' A) → Induite A := y ↦
        ⟨H.inv y, by {
          rcases y.prop with ⟨x, x_in, hx⟩; rw [←hx]
          rwa [←comp_apply (f := H.inv), H.left_inv]
        }⟩
      let G' := ofVal ∘ G; refold_let G'
      have eq : G' = H.inv ∘ ofVal := rfl
      rw [eq]; apply comp_est_continu continu_of_val
      exact H.inv_continu
    }
  }

-- Définition 3.12.

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
      · rw [M'.is_dist.symm (f y) (f x)]
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

-- 3.4. Topologie sur un ensemble produit

variable {ι : Type} {Y Z : ι → Type}

def proj : (i : ι) → (Π i, Y i) → Y i := i ↦ x ↦ (x i)

@[simp] def prod_espaces (V : (i : ι) → Partie Y i) := ⋂ i, (proj i) ⁻¹' V i

@[simp] lemma mem_prod_espaces (X : (i : ι) → Y i) (V : (i : ι) → Partie Y i) :
  X ∈ prod_espaces V ↔ ∀ i, proj i X ∈ V i := by simp

lemma proj_of_prod {X : (i : ι) → Y i} {V : (i : ι) → Partie Y i} (i : ι)
  (h : X ∈ prod_espaces V) : proj i X ∈ V i := (mem_prod_espaces X V).mp h i

open Classical in
lemma proj_prod_espaces (V : (i : ι) → Partie Y i) (i : ι) : proj i '' prod_espaces V
  = V i ∨ proj i '' prod_espaces V = ∅ := by
  by_cases h : ∀ i, V i ≠ ∅
  case pos =>
    apply Or.inl; ext x; apply Iff.intro
    · intro ⟨x', hx', hx⟩; rw [mem_prod_espaces] at hx'
      rw [←hx]; exact hx' i
    · simp only [←Set.nonempty_iff_ne_empty] at h
      intro hx; let v := i ↦ (h i).some
      use (j ↦ dite (i = j) (h ↦ h ▸ x) (_ ↦ v j))
      apply And.intro _ (by rw [proj, dif_pos (by rfl)])
      rw [mem_prod_espaces]; intro j; rw [proj]; split
      case isTrue eq =>
        suffices h : ∀ (h : i = j), h ▸ x ∈ V j from h eq
        rw [←eq]; intro _; exact hx
      case isFalse neq => apply Subtype.coe_prop
--
  case neg =>
    apply Or.inr; push_neg at h; rcases h with ⟨j, hj⟩
    unfold prod_espaces; rw [image_eq_empty, iInter_eq_empty_iff]
    have empty : proj j ⁻¹' V j = ∅ := by
      rw [←preimage_empty (f := proj j), hj]
    intro x; use j; rw [empty]; exact Set.notMem_empty x

def cofinite_eq_univ (V : (i : ι) → Partie Y i) := ∃ J : Set ι, Finite J ∧ ∀ i ∉ J,
  V i = Ω

lemma prod_eq_inter_preim {U : Partie (Π i, Y i)} {V : (i : ι) → Partie Y i}
  (hU : U = prod_espaces V) (hV : cofinite_eq_univ V) : ∃ J : Set ι, Finite J ∧
  U = ⋂ i ∈ J, (proj i) ⁻¹' V i := by
  rcases hV with ⟨J, J_fin, hJ⟩; use J, J_fin
  rw [hU, prod_espaces, ←biInter_univ, ←union_compl_self J]
  have eq_univ : ⋂ i ∈ Jᶜ, (proj i) ⁻¹' V i = Ω := by
    simp only [iInter_eq_univ]; intro i hi
    rw [hJ i hi, preimage_univ]
  rw [biInter_union, eq_univ, inter_univ]

section TopProd

variable [∀ i, EspTop (Y i)] [∀ i, EspTop (Z i)]

def top_init {X : Type} (f : (i : ι) → X → Y i) : EspTop X := topo_engendree
  {A : Set X | ∃ i : ι, ∃ U : Partie (Y i), est_ouvert U ∧ A = (f i) ⁻¹' U}

instance top_prod : EspTop (Π i, Y i) := top_init (fun i ↦ x ↦ x i)

lemma ouvert_pref_projections {X : Type} (f : (i : ι) → X → Y i) (i : ι)
  (U : Set (Y i)) (hU : est_ouvert U) : @est_ouvert X (top_init f) ((f i) ⁻¹' U) :=
  by apply ouv_top_engendree.ouvS; dsimp; exact ⟨i, U, hU, rfl⟩

@[simp] def prod_ouverts (U : Partie (Π i, Y i)) (V : (i : ι) → Partie Y i) :=
  (∀ i, est_ouvert (V i)) ∧ U = prod_espaces V

-- Définition 3.18.

def ouv_elementaire (u : Partie Π i, Y i) := ∃ V : (i : ι) → Partie Y i,
  prod_ouverts u V ∧ cofinite_eq_univ V

lemma ouv_elem_of_finite (u : Partie Π i, Y i) [Finite ι] (V : (i : ι) → Partie Y i)
  (hV : prod_ouverts u V) : ouv_elementaire u := by
  use V, hV; use Ω, finite_univ; intro i hi; absurd hi; apply mem_univ

open Classical in
lemma ouv_elem_of_preimage {i : ι} (A : Partie Y i) (h : est_ouvert A) :
  ouv_elementaire (proj i ⁻¹' A) := by
  let V := j ↦ dite (i = j) (h ↦ h ▸ A) (_ ↦ Ω)
  use V; apply And.intro
  · apply And.intro
    · intro j; by_cases eq : i = j
      · unfold V; rwa [←eq, dif_pos (refl i)]
      · unfold V; rw [dif_neg eq]; exact univ_ouvert
    · unfold prod_espaces V; simp [apply_dite, iInter_dite]
  · use {i}, Finite.of_subsingleton; intro j hj; unfold V
    rw [notMem_singleton_iff] at hj; symm at hj; rw [dif_neg hj]

lemma ouv_elem_of_univ : ouv_elementaire (Ω (α := Π i, Y i)) := by
  use j ↦ Ω, (by simp); use ∅, finite_empty; intro i hi; rfl

lemma ouv_elem_of_inter {u v : Partie Π i, Y i} (h₁ : ouv_elementaire u)
  (h₂ : ouv_elementaire v) : ouv_elementaire (u ∩ v) := by
  rcases h₁ with ⟨U, ⟨U_ouv, hU⟩, ⟨J₁, J_fin₁, hJ₁⟩⟩
  rcases h₂ with ⟨V, ⟨V_ouv, hV⟩, ⟨J₂, J_fin₂, hJ₂⟩⟩
  use i ↦ U i ∩ V i; apply And.intro
  · dsimp; apply And.intro
    · intro i; exact inter_ouvert (U_ouv i) (V_ouv i)
    · rw [hU, hV]; simp [iInter_inter_distrib]
  · use J₁ ∪ J₂, Finite.union J_fin₁ J_fin₂
    intro i hi; rw [mem_union, not_or] at hi; dsimp
    rw [hJ₁ i hi.1, hJ₂ i hi.2, inter_univ]

open Classical in
lemma ouv_elem_of_empty [ne : Nonempty ι] : ouv_elementaire (∅ : Partie (Π i, Y i))
  := by
  let i := Nonempty.some ne
  let V : (j : ι) → Partie Y j := j ↦ ite (i = j) ∅ Ω
  use V; dsimp [V]; apply And.intro
  · apply And.intro
    · intro j; by_cases eq : i = j
      · rw [if_pos eq]; exact empty_ouvert
      · rw [if_neg eq]; exact univ_ouvert
    · simp [apply_ite, iInter_ite]
  · use {i}, Finite.of_subsingleton; intro j hj; dsimp
    rw [notMem_singleton_iff] at hj; symm at hj; rw [if_neg hj]

lemma ouv_of_ouv_elem (U : Partie (Π i, Y i)) (h : ouv_elementaire U) :
  est_ouvert U := by
  rcases h with ⟨V, ⟨V_ouv, hV⟩, cofin⟩
  rcases prod_eq_inter_preim hV cofin with ⟨J, hJ, eq⟩
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

-- Théorème 3.20.

-- a)

theorem continu_of_proj (i : ι) : est_continu (proj (Y := Y) i) := by
  rw [continu_iff_preim_ouv]; intro U hU
  apply ouvert_pref_projections; exact hU

theorem ouverte_of_proj (i : ι) : est_fun_ouverte (proj (Y := Y) i) := by
  intro s hs; apply ouv_eq_elem_union at hs
  rcases hs with ⟨V, hV, hs⟩; rw [hs, image_sUnion]
  apply sUnion_ouvert; intro t ⟨v, hv, ht⟩; rw [←ht]
  unfold ouv_elementaire prod_ouverts at hV
  rcases hV v hv with ⟨W, ⟨W_ouv, W_prod⟩, W_fin⟩
  rw [W_prod]; cases proj_prod_espaces W i
  case inl h => rw [h]; exact W_ouv i
  case inr h => rw [h]; exact empty_ouvert

-- b)

theorem continu_iff_proj_continu (f : X → Π i, Y i) : est_continu f ↔ ∀ i, est_continu
  (proj i ∘ f) := by
  apply Iff.intro
  · intro h i; apply comp_est_continu (hf := h); apply continu_of_proj
  · intro h x V hV; rw [vois_of_prod] at hV
    rcases hV with ⟨u, u_in, hu, x_in⟩; use f ⁻¹' u; apply And.intro
    · apply ouv_est_vois (u := f ⁻¹' u) _ x_in
      rcases hu with ⟨W, ⟨W_ouv, hW⟩, cofin⟩
      rcases prod_eq_inter_preim hW cofin with ⟨J, hJ, eq⟩
      rw [eq, preimage_iInter₂]; apply inter_fini_ouvert; intro i hi
      rw [←preimage_comp]; exact ouv_preim_of_continu (h i) (W_ouv i)
    · apply le_trans _ u_in; apply image_preimage_subset

-- topologie induite sur un produit :

def prod_fun (F : (i : ι) → Y i → Z i) : (Π i, Y i) → Π i, Z i := P ↦ i ↦ F i (P i)

omit [∀ i, EspTop (Y i)] [∀ i, EspTop (Z i)] in
lemma proj_ofFun_eq_fun {F : (i : ι) → Y i → Z i} (i : ι) : proj i ∘ (prod_fun F) =
  (F i) ∘ (proj i) := by rfl

def prod_induite (V : (i : ι) → Partie Y i) : ι → Type := i ↦ Induite (V i)

def ofVal_prod {V : (i : ι) → Partie Y i} : (Π i, prod_induite V i) → Π i, Y i :=
  prod_fun (_ ↦ Subtype.val)

omit [∀ i, EspTop (Y i)] [∀ i, EspTop (Z i)] in
lemma proj_ofVal_eq_val {V : (i : ι) → Partie Y i} (i : ι) : proj i ∘ ofVal_prod =
  ofVal ∘ (proj (Y := prod_induite V) i) := proj_ofFun_eq_fun i

omit [∀ i, EspTop (Y i)] [∀ i, EspTop (Z i)] in
lemma range_ofVal_prod (V : (i : ι) → Partie Y i) : range (ofVal_prod (V := V)) =
  prod_espaces V := by
  ext x; rw [mem_prod_espaces]; apply Iff.intro
  · intro ⟨P, hP⟩ i; rw [←hP]; exact (P i).prop
  · intro h; use i ↦ ⟨proj i x, h i⟩; rfl

omit [∀ i, EspTop (Y i)] [∀ i, EspTop (Z i)] in
lemma ofVal_prod_of_prod {V : (i : ι) → Partie Y i} (Q : Π i, prod_induite V i) :
  ofVal_prod Q ∈ prod_espaces V := by
  rw [←range_ofVal_prod, mem_range]; use Q

instance ofProdInd {V : (i : ι) → Partie Y i} : EspTop (Π i, prod_induite V i) :=
  @top_prod _ _ (_ ↦ ofInd)

lemma continu_of_val_prod (V : (i : ι) → Partie Y i) : est_continu (ofVal_prod
  (V := V)) := by
  rw [continu_iff_proj_continu]; intro i
  rw [proj_ofVal_eq_val]; apply comp_est_continu
  · exact @continu_of_proj _ _ (_ ↦ ofInd) i
  · exact continu_of_val

instance prodHomeo [Homeo : ∀ i, Homeomorphe (Y i) (Z i)]
  (H := i ↦ (Homeo i).est_homeo) : Homeomorphe (Π i, Y i) (Π i, Z i) where
  homeo := P ↦ i ↦ (Homeo i).homeo (P i)
  est_homeo := {
    inv := Q ↦ i ↦ (H i).inv (Q i)
    left_inv := by {
      ext f i; apply left_inverse_of_homeo_inv
    }
    right_inv := by {
      ext f i; apply right_inverse_of_homeo_inv
    }
--
    continu := by {
      rw [continu_iff_proj_continu]; intro i
      let F := (i : ι) ↦ (Homeo i).homeo
      have eq : prod_fun F = P ↦ i ↦ (Homeo i).homeo (P i) := by rfl
      rw [←eq, proj_ofFun_eq_fun (F := F)]
      apply comp_est_continu (continu_of_proj i); exact (H i).continu
    }
    inv_continu := by {
      rw [continu_iff_proj_continu]; intro i
      let F := (i : ι) ↦ (H i).inv
      have eq : prod_fun F = Q ↦ i ↦ (H i).inv (Q i) := by rfl
      rw [←eq, proj_ofFun_eq_fun (F := F)]
      apply comp_est_continu (continu_of_proj i); exact (H i).inv_continu
    }
  }

instance homeo_prod_induite {V : (i : ι) → Partie Y i} : Homeomorphe
  (Induite (prod_espaces V)) (Π i, prod_induite V i) where
  homeo := P ↦ i ↦ ⟨P.val i, proj_of_prod i P.prop⟩
  est_homeo := {
    inv := Q ↦ ⟨ofVal_prod Q, ofVal_prod_of_prod Q⟩
    left_inv := by ext x i; simp; rfl
    right_inv := by ext x i; simp; rfl

    continu := by {
      rw [continu_iff_proj_continu]; intro i
      rw [continu_iff_val_continu]
      let F : (Induite (prod_espaces V)) → (Π i, prod_induite V i)
            := P ↦ i ↦ ⟨P.val i, proj_of_prod i P.prop⟩
      let p := ofVal ∘ (proj i) ∘ F; refold_let p
      have eq : p = (proj i) ∘ ofVal := by rfl
      rw [eq]; apply comp_est_continu continu_of_val
      exact continu_of_proj i
    }

    inv_continu := by {
      rw [continu_iff_val_continu]; exact continu_of_val_prod V
    }
  }

end TopProd

-- Exemple 3.21.

-- a)

section MetProd

def MetProd {ι : Type} (Y : ι → Type) [∀ i, EspaceMetrique (Y i)] [Nonempty ι]
  [Finite ι] := Π i, Y i

def MetProdFin {n} (_ : n > 0) (Y_n : Fin n → Type) [∀ i, EspaceMetrique (Y_n i)]
  := Π i, Y_n i

noncomputable def metrique_of_prod_metrique [M : ∀ i, EspaceMetrique (Y i)]
  [h : Nonempty ι] [Finite ι] : EspaceMetrique (MetProd Y) := by
  let S (x y : (Π i, Y i)) : Set ℝ := {d(x i, y i) | i}
  have bdd_above (x y : (Π i, Y i)) : BddAbove {d(x i, y i) | i} := by
    apply SupReal.bddabove_of_finite_image'
  have bdd_below (x y : (Π i, Y i)) : BddBelow {d(x i, y i) | i} := by
    apply SupReal.bddbelow_of_finite_image'
  let d : (Π i, Y i) → (Π i, Y i) → ℝ := x ↦ y ↦ sSup {d(x i, y i) | i}
--
  use d; unfold MetProd; rcases h with ⟨i⟩; constructor
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
  [Finite ι] : EspaceMetrique (MetProd Y) := metrique_of_prod_metrique

noncomputable instance instProdFin {n} (h : n > 0) (Y_n : Fin n → Type) [M : ∀ i,
  EspaceMetrique (Y_n i)] : EspaceMetrique (MetProdFin h Y_n) := instProd (h := ⟨0, h⟩)

lemma prod_dist [∀ i, EspaceMetrique (Y i)] [h : Nonempty ι] [Finite ι] (x y :
  MetProd Y) : d(x, y) = sSup {d(x i, y i) | i} := by rfl

lemma le_prod_dist [∀ i, EspaceMetrique (Y i)] [h : Nonempty ι] [Finite ι]
  (x y : MetProd Y) : ∀ i, d(x i, y i) ≤ d(x, y) := by
  intro i; rw [prod_dist]; apply le_csSup _ (by use i)
  apply SupReal.bddabove_of_finite_image'

variable [∀ i, EspaceMetrique (Y i)] [nempty : Nonempty ι] [Finite ι]
variable {n : ℕ} {Y_n : Fin n → Type} {h : n > 0} [∀ i, EspaceMetrique (Y_n i)]

theorem ouv_elem_of_boule (a : MetProd Y) (r : ℝ) : ouv_elementaire
  (Bₒ (X := MetProd Y) a r) := by
  apply ouv_elem_of_finite (V := i ↦ Bₒ (a i) r)
  dsimp; apply And.intro
  · intro i; exact ouv_of_boule_ouv (a i) r
  · ext x; apply Iff.intro
    · intro h; rw [mem_iInter]; intro i
      exact lt_of_le_of_lt (le_prod_dist x a i) h
    · intro h; dsimp; rw [prod_dist, Finite.csSup_lt_iff]
      · intro z ⟨i, hi⟩; rw [←hi]; rw [mem_iInter] at h; exact h i
      · apply SupReal.image_of_fin
      · let i := Nonempty.some nempty; use d(x i, a i); use i

lemma ouv_of_top_prod_iff_ouv_of_met : ∀ s : Partie Π i, Y i, est_ouvert s ↔
  est_ouvert (X := MetProd Y) s := by
  intro s; apply Iff.intro
  · intro h a ha; rw [ouvert_ssi_vois] at h
    specialize h a ha; rw [vois_of_prod] at h
    rcases h with ⟨U, U_in, ⟨p, ⟨p_ouv, hp⟩, _⟩, a_in⟩
    rw [hp, mem_prod_espaces] at a_in
    have exists_r : ∀ i, ∃ r > 0, Bₒ (a i) r ⊆ p i := by
      intro i; apply p_ouv i; exact a_in i
    choose f hf₁ hf₂ using exists_r; let S := range f
--
    let i := Nonempty.some nempty
    have hn : S.Nonempty := by use (f i); use i
    have hf : Finite S := by apply SupReal.image_of_fin
    use sInf S; apply And.intro
    · rw [gt_iff_lt, Finite.lt_csInf_iff hf hn]
      intro x ⟨j, hj⟩; rw [←hj]; exact hf₁ j
    · intro x hx; apply U_in; rw [hp, mem_prod_espaces]
      intro j; apply hf₂; dsimp; apply lt_of_le_of_lt
      · exact le_prod_dist x a j
      · apply lt_of_lt_of_le hx; apply csInf_le _ (by use j)
        apply SupReal.bddbelow_of_finite_image'
--
  · intro h; rw [ouvert_ssi_vois]; intro x hx
    rw [vois_of_prod]; rcases h x hx with ⟨r, r_pos, hr⟩
    use Bₒ (X := MetProd Y) x r, hr, ouv_elem_of_boule x r
    exact centre_in_boule (X := MetProd Y) x r_pos

noncomputable instance homeo_met_prod : Homeomorphe (Π i, Y i) (MetProd Y) :=
  of_ouv_iff_ouv id bijective_id (by {
    intro s; rw [ouv_of_top_prod_iff_ouv_of_met, image_id]
  })

noncomputable instance homeo_ind_met_prod {A : Partie Π i, Y i} : Homeomorphe
  (Induite A) (Induite (X := MetProd Y) A) := by
  suffices h : Homeomorphe (Induite A) (Induite (X := MetProd Y) (id '' A))
  by rwa [image_id] at h
  apply ind_homeo_ind A (H := homeo_met_prod.est_homeo)

noncomputable instance homeo_prod_fin : Homeomorphe (Π i, Y_n i) (MetProdFin h Y_n) :=
  homeo_met_prod (nempty := ⟨0, h⟩)

noncomputable instance homeo_ind_prod_fin {A : Partie Π i, Y_n i} : Homeomorphe
  (Induite A) (Induite (X := MetProdFin h Y_n) A) := homeo_ind_met_prod (nempty := ⟨0, h⟩)

-- le cas des e.v.n. réelles (de dimension n > 0)

instance Rn_homeo_prod : Homeomorphe (ℝ^n) (MetProdFin h (_ ↦ ℝ)) where
  homeo := x ↦ x.p
  est_homeo := {
    inv := y ↦ ⟨y⟩
    left_inv := rfl
    right_inv := rfl

    continu := by {
      rw [continu_iff_preim_ouv]; intro U h
      intro x x_in; let y := x.p
      have y_in : y ∈ U := by apply x_in
      rcases h y y_in with ⟨r, r_pos, hr⟩
      use r, r_pos; intro x' x'_in; exact hr x'_in
    }

    inv_continu := by {
      rw [continu_iff_preim_ouv]; intro U h
      intro y y_in; let x : ℝ^n := ⟨y⟩
      have x_in : x ∈ U := by apply y_in
      rcases h x x_in with ⟨r, r_pos, hr⟩
      use r, r_pos; intro y' y'_in; exact hr y'_in
    }
  }

lemma Rn_borne_iff_prod_borne (A : Partie ℝ ^ n) : letI f : ℝ^n → MetProdFin h (_ ↦ ℝ)
  := x ↦ x.p; est_borne A ↔ est_borne (f '' A) := by
  apply Iff.intro
  · intro h; rcases h with ⟨M, M_nneg, hM⟩
    use M, M_nneg; intro w hw z hz
    rcases hw with ⟨x, x_in, hx⟩; rcases hz with ⟨y, y_in, hy⟩
    rw [←hx, ←hy]; apply hM x x_in y y_in
  · intro h; rcases h with ⟨M, M_nneg, hM⟩
    use M, M_nneg; intro x hx y hy
    apply hM x.p (by use x) y.p (by use y)

lemma vois_of_top_iff_vois_of_met (x : Π i, Y i) (X : Partie Π i, Y i) : est_vois x X
  ↔ est_vois (X := MetProd Y) x X := by
  nth_rw 2 [←image_id X]; apply vois_iff_homeo_vois

lemma conv_top_iff_conv_met (u : ℕ → Π i, Y i) (l : Π i, Y i) : converge_vers u l
  ↔ converge_vers (X := MetProd Y) u l := conv_iff_homeo_conv u l

theorem conv_to_in_prod (u : ℕ → MetProd Y) (l : MetProd Y) : converges_to u l ↔
  ∀ i, converges_to (n ↦ (u n) i) (l i) := by
  apply Iff.intro
  · intro h; rw [←conv_vers_iff_conv_to] at h
    simp only [←conv_vers_iff_conv_to]
    rwa [←conv_top_iff_conv_met, conv_vers_in_prod] at h
  · intro h; simp only [←conv_vers_iff_conv_to] at *
    rw [←conv_vers_in_prod] at h; rwa [←conv_top_iff_conv_met]

theorem converges_in_prod (u : ℕ → MetProd Y) : converges u ↔ ∀ i, converges
  (n ↦ (u n) i) := by
  apply Iff.intro
  · intro ⟨l, hl⟩ i; use l i; rw [conv_to_in_prod] at hl; exact hl i
  · intro h; choose l hl using h; use l; rwa [←conv_to_in_prod] at hl

theorem prod_borne_iff_borne (A : Partie MetProd Y) : est_borne A ↔ ∀ i, est_borne
  (proj i '' A) := by
  apply Iff.intro
  · intro ⟨M, M_nneg, hM⟩ k; use M, M_nneg
    intro x ⟨i, i_in, hi⟩ y ⟨j, j_in, hj⟩
    rw [←hi, ←hj]; apply le_trans _ (hM i i_in j j_in)
    exact le_prod_dist i j k
  · intro hi; choose f hf hf' using hi
    let i := nempty.some
    use sSup {f i | i}; apply And.intro
    · apply le_csSup_of_le (b := f i) _ (by use i) (hf i)
      apply SupReal.bddabove_of_finite_image'
    · intro x hx y hy; rw [prod_dist]; apply csSup_le
      · use d(x i, y i); use i
      · intro d ⟨j, hj⟩; rw [←hj]
        have x_in : (x j) ∈ proj j '' A := by use x, hx; rfl
        have y_in : (y j) ∈ proj j '' A := by use y, hy; rfl
        apply le_trans (hf' j (x j) x_in (y j) y_in)
        apply le_csSup _ (by use j); apply SupReal.bddabove_of_finite_image'

end MetProd

-- Proposition 3.23.

abbrev X_square (X : Type) [EspTop X] := Π _ : Fin 2, X
notation : max X "²" => X_square X

abbrev p1 (x : X²) : X := x (0 : Fin 2)
abbrev p2 (x : X²) : X := x (1 : Fin 2)

def diagonale (X : Type) [T : EspTop X] : Partie X² := {x | p1 x = p2 x}
notation : max "Δ" X : max => diagonale X

def prod_in_square (U V : Partie X) : Partie X² := {x | p1 x ∈ U ∧ p2 x ∈ V}
notation U : max " ×₂ " V : max => prod_in_square U V

def prod_pair (U V : Partie X) : Fin 2 → Partie X := n ↦ match n with
  | 0 => U
  | 1 => V
notation U : max " ×² " V : max => prod_pair U V

lemma prod_eq_prod₂ (U V : Partie X) : U ×₂ V = prod_espaces (U ×² V) := by
  unfold prod_pair prod_in_square prod_espaces; ext x
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
    rw [h₂, mem_prod_espaces, Fin.forall_fin_two] at in_U
    apply And.intro in_U.1; apply And.intro in_U.2
    rwa [h₂, prod₂_eq_prod, subset_compl_diagonale] at U_in
