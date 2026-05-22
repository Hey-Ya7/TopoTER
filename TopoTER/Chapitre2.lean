import TopoTER.Chapitre1

open TER

-- 2. Espaces topologiques

-- Définition 2.1.

open Set

class EspTop (X : Type*) where
  est_ouvert : Set X → Prop
  univ_ouvert : est_ouvert Ω
  empty_ouvert : est_ouvert ∅
--
  union_ouvert {ι : Type u_1} {F : Famille ι X} (hu : ∀ A ∈ F, est_ouvert A) :
    est_ouvert (⋃ᵢ F)
--
  inter_ouvert {u v : Set X} (hu : est_ouvert u) (hv : est_ouvert v) :
    est_ouvert (u ∩ v)

attribute [simp] EspTop.univ_ouvert EspTop.empty_ouvert

variable {X Y : Type*} [EspTop X] [EspTop Y]

namespace EspTop

lemma iunion_ouvert {ι : Type u_1} {u : ι → Set X} (h : ∀ i, est_ouvert (u i)) :
  est_ouvert (⋃ i, u i) := by
  let F : Famille ι X := ⟨u⟩
  have eq : ⋃ᵢ F = ⋃ i, u i := by rfl
  have hu : ∀ A ∈ F, est_ouvert A := by
    intro A hA; rcases hA with ⟨i, hi⟩
    rw [←hi]; exact h i
  rw [←eq]; exact union_ouvert (ι := ι) hu

lemma bunion_ouvert {ι : Type u_1} {u : ι → Set X} {I : Set ι} (h : ∀ i ∈ I,
  est_ouvert (u i)) : est_ouvert (⋃ i ∈ I, u i) := by
  apply iunion_ouvert; intro i
  by_cases hi : i ∈ I
  · simp [hi, h]
  · simp only [hi, iUnion_of_empty]
    exact empty_ouvert

lemma union_est_ouvert (u v : Set X) (hu : est_ouvert u) (hv : est_ouvert v) :
  est_ouvert (u ∪ v) := by
  let P : Set (Set X) := {u, v}
  have union_F : ⋃ x ∈ P, x = u ∪ v := by
    ext x; simp only [mem_iUnion, exists_prop]
    apply Iff.intro
    · case mp => intro h; rcases h with ⟨s, hs, x_in⟩
                 cases hs; repeat simp_all
    · case mpr => intro h; cases h
                  · case inl => use u, Or.inl (refl u)
                  · case inr => use v, Or.inr (refl v)
--
  rw [←union_F]; apply bunion_ouvert; intro s hs
  cases hs; repeat simp_all

lemma inter_fini_ouvert {ι : Type*} {u : ι → Set X} {I : Set ι} [hI : Finite I]
  (h : ∀ i ∈ I, est_ouvert (u i)) : est_ouvert (⋂ i ∈ I, u i) := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | @insert x s hs hx H =>
      rw [biInter_insert x s u]
      apply inter_ouvert
      · apply h; exact mem_insert x s
      · apply H; intro i hi; apply h
        exact mem_insert_of_mem x hi

lemma inter_fini_ouvert' {ι : Type*} {u : ι → Set X} [Finite ι] (h : ∀ i,
  est_ouvert (u i)) : est_ouvert (⋂ i, u i) := by
  have eq : ⋂ i ∈ Ω, u i = ⋂ i, u i := by simp
  rw [←eq]; apply inter_fini_ouvert (I := Ω); intro i hi; exact h i

@[simp] def est_ferme (s : Set X) := est_ouvert sᶜ

lemma est_ouvert_iff_compl_est_ferme {s : Set X} : est_ouvert s ↔ est_ferme sᶜ
  := by rw [est_ferme, compl_compl]

@[simp] lemma univ_est_ferme : est_ferme (univ : Set X) := by
  rw [est_ferme, compl_univ]
  exact empty_ouvert

@[simp] lemma empty_est_ferme : est_ferme (∅ : Set X) := by
  rw [est_ferme, compl_empty]
  exact univ_ouvert

open Famille in
lemma inter_ferme {ι : Type u_1} {F : Famille ι X} (hu : ∀ A ∈ F, est_ferme A) :
  est_ferme (⋂ᵢ F) := by
  rw [est_ferme, inter_famille_compl]
  apply union_ouvert; intro A hA; rw [in_compl_famille] at hA
  rw [est_ouvert_iff_compl_est_ferme]; apply hu Aᶜ hA

lemma union_ferme {u v : Set X} (hu : est_ferme u) (hv : est_ferme v) :
  est_ferme (u ∪ v) := by
  rw [est_ferme, compl_union]
  apply inter_ouvert; repeat assumption

lemma inter_est_ferme {ι : Type u_1} {u : ι → Set X} (hu : ∀ i, est_ferme (u i)) :
  est_ferme (⋂ i, u i) := by
  rw [est_ferme, compl_iInter]
  exact iunion_ouvert hu

lemma union_fini_ferme {ι : Type} {u : ι → Set X} {I : Set ι} [Finite I]
  (h : ∀ i ∈ I, est_ferme (u i)) : est_ferme (⋃ i ∈ I, u i) := by
  rw [est_ferme, compl_iUnion₂]
  exact inter_fini_ouvert h

lemma union_fini_ferme' {ι : Type} {u : ι → Set X} [Finite ι]
  (h : ∀ i, est_ferme (u i)) : est_ferme (⋃ i, u i) := by
  rw [est_ferme, compl_iUnion]
  exact inter_fini_ouvert' h

-- Exemple 2.2.

-- a)

open Metrique
instance {X : Type*} [EspaceMetrique X] : EspTop X where
  est_ouvert := A ↦ ouverte A
  univ_ouvert := ouverte_of_uni
  empty_ouvert := ouverte_of_vide

  union_ouvert := ouverte_of_union
  inter_ouvert := ouverte_of_inter

-- 2.2. Intérieur, adhérence, voisinage

structure est_vois_ouv_dans {X : Type*} [EspTop X] (x : X) (s ouv : Set X) where
  x_dans : x ∈ ouv
  ouv_ouvert : est_ouvert ouv
  ouv_contenu : ouv ⊆ s

def est_vois {X : Type*} [EspTop X] (x : X) (s : Set X) :=
  ∃ u, est_vois_ouv_dans x s u

lemma ouvert_ssi_vois (s : Set X) : est_ouvert s ↔ ∀ x ∈ s, est_vois x s := by
  apply Iff.intro
  · case mp => intro h x hx; use s
               exact ⟨hx, h, subset_refl s⟩
  · case mpr =>
      intro h; choose! u hu using h
      have union : s = ⋃ x ∈ s, u x := by
        ext x; simp only [mem_iUnion, exists_prop]
        apply Iff.intro
        · intro hx; use x; apply And.intro hx
          exact ((hu x) hx).x_dans
        · intro h; rcases h with ⟨i, hi, hx⟩
          specialize hu i hi; exact hu.ouv_contenu hx
      rw [union]; apply bunion_ouvert; intro x x_in
      exact (hu x x_in).ouv_ouvert

lemma ouv_est_vois {x : X} {u : Set X} : est_ouvert u → x ∈ u → est_vois x u := by
  intro u_ouv x_u
  use u
  exact ⟨x_u, u_ouv, by simp⟩

@[simp] def adh (s : Set X) := {x | ∀ u, est_vois x u → (u ∩ s).Nonempty}

lemma contenu_adh (s : Set X) : s ⊆ adh s := by
  intro x hx U hxU
  use x
  constructor
  · rcases hxU with ⟨V, hV⟩
    apply hV.ouv_contenu
    exact hV.x_dans
  exact hx

lemma adh_eq_inter (s : Set X) : adh s = ⋂₀ {F : Set X | est_ferme F ∧ s ⊆ F} := by
  apply Subset.antisymm_iff.mpr
  constructor
  · intro x hasx F hF
    simp only [mem_setOf_eq, est_ferme] at hF; rcases hF with ⟨hF1, hF2⟩;
    by_contra hxnh; rw[← mem_compl_iff] at hxnh; rw[ouvert_ssi_vois] at hF1; specialize hF1 x hxnh;
    specialize hasx (Fᶜ) hF1
    have subs_nempty : (Fᶜ ∩ s) ⊆ Fᶜ ∩ F := inter_subset_inter_right (Fᶜ) hF2
    have hne : (Fᶜ ∩ F).Nonempty := Nonempty.mono subs_nempty hasx
    rw[nonempty_iff_ne_empty, inter_comm] at hne
    exact hne (inter_compl_self F)
  rintro x hx U ⟨V, ⟨h1, h2, h3⟩⟩
  have HVUS : V ∩ s ⊆ U ∩ s := by exact inter_subset_inter_left s h3
  apply Nonempty.mono HVUS
  by_contra! h;
  have hVc : est_ferme Vᶜ := est_ouvert_iff_compl_est_ferme.mp h2
  rw[← Set.subset_empty_iff, ← Set.disjoint_iff, ← subset_compl_iff_disjoint_left] at h
  have : x ∈ Vᶜ := by
    apply hx
    exact mem_sep hVc h
  exact this h1

lemma adh_ferme (s : Set X) : est_ferme (adh s) := by
  rw [adh_eq_inter, sInter_eq_iInter]
  apply inter_est_ferme
  intro F
  exact F.property.1

----------------------------------------------------------------------------------------------
@[simp]
def int (s : Set X) := {x | est_vois x s}

lemma ouvert_iff_int (U : Set X) : est_ouvert U ↔ (int U) = U := by
  constructor
  · intro hU
    unfold int
    ext x
    constructor
    · intro hx
      rcases hx with ⟨_,⟨h1, _, h2⟩⟩
      exact mem_of_subset_of_mem h2 h1
    · exact fun hx ↦ ⟨U, hx, hU, by simp⟩
  rw [ouvert_ssi_vois]
  intro h x hx
  rw [<-h] at hx
  unfold int at hx
  exact hx

@[simp]
def front (s : Set X) := (adh s)\(int s)

lemma front_carac (U : Set X) : front U = (adh U) ∩ (adh (Uᶜ)) := by
  unfold front
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    constructor
    · exact hx1
    · simp only [adh, mem_setOf_eq]
      intro V hV
      by_contra h
      absurd hx2
      rcases hV with ⟨v, x_dans, ouv_ouvert, ouv_contenu⟩
      use v
      constructor
      · exact x_dans
      · exact ouv_ouvert
      · rw [inter_compl_nonempty_iff] at h
        push_neg at h
        apply subset_trans ouv_contenu h
  · rintro ⟨hx1, hx2⟩
    constructor
    · exact hx1
    · simp only [int, mem_setOf_eq]
      by_contra! h
      specialize hx2 U h
      rw [inter_comm, compl_inter_self U] at hx2
      choose y hy using hx2
      exact hy

structure base_de_vois {X : Type*} [EspTop X] (x : X) {ι : Type} (V : ι → Set X) where
  V_vois : ∀(i : ι), est_vois x (V i)
  V_base : ∀(W : Set X), est_vois x W → ∃(i : ι), (V i) ⊆ W

-- 2.3. Suites dans un espace topologique ou métrique

def converge_vers (u : ℕ -> X) (l : X) :=
∀ V : Set X, est_vois l V → ∃ n : ℕ, ∀ m : ℕ, m ≥ n → u m ∈ V

lemma conv_equ_ouv (u : ℕ -> X) (l : X) : converge_vers u l ↔
∀ V : Set X, (est_vois l V ∧ est_ouvert V) → ∃ n : ℕ, ∀ m : ℕ, m ≥ n → u m ∈ V := by
  constructor
  · intro conv V hV
    exact conv V hV.1
  · intro h V hV
    rcases hV with ⟨W, l_W, W_ouv, W_V⟩
    have hW : est_vois l W ∧ est_ouvert W := ⟨by use W; exact ⟨l_W, W_ouv, by rfl⟩, W_ouv⟩
    specialize h W hW
    rcases h with ⟨n, hn⟩
    use n
    intro m hm
    specialize hn m hm
    exact W_V hn

def converge (u : ℕ → X) := ∃ l : X, converge_vers u l

--lemma ferme_suite (F : Set X) : est_ferme F ↔ (∀ u : ℕ → F, ∃ l : F, converge_vers u l)

class EspSepareT2 (X : Type*) [EspTop X] where
  est_separe : ∀ (x y : X), x ≠ y → ∃ (U V : Set X),
    (est_ouvert U) ∧ (est_ouvert V) ∧ (x ∈ U) ∧ (y ∈ V) ∧ (U ∩ V = ∅)

variable {Z : Type*} [EspTop Z] [S : EspSepareT2 Z]

instance {X : Type*} [M : EspaceMetrique X] : EspSepareT2 X where
  est_separe := by
    intro x y h; let d := d(x, y) / 2
    have d_pos : d > 0 := by
      apply half_pos; apply lt_of_le_of_ne
      · exact M.is_dist.nneg x y
      · intro eq; apply h; rw [←M.is_dist.sep, eq]
--
    let B1 := Bₒ x d; let B2 := Bₒ y d
    use B1, B2, ouv_of_boule_ouv x d, ouv_of_boule_ouv y d,
            centre_in_boule x d_pos, centre_in_boule y d_pos
    apply eq_empty_of_forall_notMem; intro z hz
    have ineq₁ : d(z, x) < d := hz.left
    have ineq₂ : d(z, y) < d := hz.right
    have ineq₃ := M.is_dist.ineq x z y
    rw [M.is_dist.symm] at ineq₁
    unfold d at ineq₁; unfold d at ineq₂; linarith

lemma unicite_lim (u : ℕ → Z) (l l' : Z) :
(converge_vers u l ∧ converge_vers u l') → l = l' := by
  contrapose!
  intro hll' hul
  unfold converge_vers at *
  rcases S.est_separe l l' hll' with ⟨U, V, hU, hV, hx, hy ,hUV⟩
  specialize hul U (ouv_est_vois hU hx)
  push_neg
  use V
  constructor
  · exact ouv_est_vois hV hy
  · rcases hul with ⟨N, hN⟩
    intro n
    let k := max N n
    use k
    constructor
    · exact Nat.le_max_right N n
    · specialize hN k (Nat.le_max_left N n)
      intro h
      have hk : u k ∈ U ∩ V := mem_inter hN h
      have H : U ∩ V ≠ ∅ := ne_of_mem_of_not_mem' hk fun a ↦ a
      contradiction

def dense (X : Type*) [EspTop X] (A : Set X) : Prop := adh A = univ

lemma dense_iff_inter_ouvert_nonempty (s : Set X) :
dense X s ↔ ∀ V, est_ouvert V → V.Nonempty → (V ∩ s).Nonempty := by
  constructor
  · rintro s_dens V V_ouv ⟨x, hxV⟩
    have hxs : x ∈ (adh s) := by
      rw [s_dens]
      exact mem_univ x
    have V_vois : est_vois x V := ⟨V, hxV, V_ouv, fun y hy ↦ hy⟩
    exact hxs V V_vois
  · intro h
    unfold dense
    apply Subset.antisymm_iff.mpr
    constructor
    · exact (fun x _ ↦ mem_univ x)
    · rintro x _ u ⟨v, ⟨x_in_v, v_ouv, v_in_u⟩⟩
      have v_ne : v.Nonempty := by use x
      specialize h v v_ouv v_ne
      exact Nonempty.mono (inter_subset_inter_left s v_in_u) h

variable {E : Type*} [EspTop E]

def val_adh (u : ℕ → E) (x : E) : Prop :=
 ∀(V : Set E), est_vois x V → ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ (u n) ∈ V

lemma val_adh_inter (u : ℕ → E) :
let X := fun (k : ℕ) ↦ {x : E | ∃ n ≥ k, u n = x}
{x : E | val_adh u x} = ⋂ n : ℕ, adh (X n) := by
  intro X
  ext x
  constructor
  · intro hx
    rw[Set.mem_iInter]
    intro i
    rw[Set.mem_setOf] at hx; unfold val_adh at hx
    unfold adh
    rw[Set.mem_setOf]
    intro V hVVois
    specialize hx V hVVois
    specialize hx i
    rcases hx with ⟨n, ⟨hni, hnV⟩⟩
    --rw[nonempty_iff_empty_ne]
    have h : u n ∈ X i := by
      rw[Set.mem_setOf]
      use n
    apply inter_nonempty.mpr
    use u n
  · intro hx
    rw[Set.mem_setOf]; unfold val_adh
    intro V hV m
    rw[Set.mem_iInter] at hx
    specialize hx m
    unfold adh at hx
    rw[Set.mem_setOf] at hx
    specialize hx V hV
    rw[Set.nonempty_def] at hx
    rcases hx with ⟨y, ⟨hyVn, hyXm⟩⟩
    rw[Set.mem_setOf] at hyXm
    rcases hyXm with ⟨n, ⟨hnm, huny⟩⟩
    use n
    constructor
    · exact hnm
    exact mem_of_eq_of_mem huny hyVn

noncomputable def construction_extract_phi {X : Type*} [EspaceMetrique X]
  (u : ℕ → X) (x : X) (h : val_adh u x) : ℕ → ℕ
  | 0 => 0
  | Nat.succ k =>
      let prev := construction_extract_phi u x h k
      let A := {m : ℕ | m > prev ∧ u m ∈ Bₒ x (1/(k+1))}
      have A_ne : ∃ l, l ∈ A := by
        have hk1_pos : (0 : ℝ) < 1/(k+1):= by
          apply one_div_pos.mpr;
          exact Nat.cast_add_one_pos k
        have est_vois_B : est_vois x (Bₒ x (1/(k+1))) := by
          apply ouv_est_vois
          · exact ouv_of_boule_ouv x (1/(k+1))
          · exact centre_in_boule x hk1_pos
        specialize h (Bₒ x (1/(k+1))) est_vois_B
        specialize h ((prev) + 1)
        rcases h with ⟨l, ⟨hlφ, hl⟩⟩
        use l; apply And.intro _ hl
        change (prev) + 1 ≤ l at hlφ
        change prev < l
        rwa [Nat.lt_iff_add_one_le]
      let dec := Classical.decPred (· ∈ A); Nat.find A_ne

theorem val_adh_iff_extraite_conv {X : Type*} [EspaceMetrique X] (u : ℕ → X) (x : X) :
  val_adh u x ↔ ∃ φ, extraction φ ∧ converge_vers (u ∘ φ) x := by
 constructor
 · intro hvadhx
   let φ := construction_extract_phi u x hvadhx
   use φ; unfold φ; constructor
   · rw [extract_equiv]
     intro n; let prev := construction_extract_phi u x hvadhx n
     refold_let prev; unfold construction_extract_phi
     let p := m ↦ m > prev ∧ u m ∈ Bₒ x (1/(n + 1))
     let dec := Classical.decPred p; apply And.left
     apply Nat.find_spec (p := p)
   · unfold converge_vers
     have inegφ : ∀ n : ℕ, d((u ∘ φ) (n + 1), x) < 1/(n+1):= by
      intro n; change u (φ (n + 1)) ∈ Bₒ x (1/(n + 1))
      let prev := construction_extract_phi u x hvadhx n
      let p := m ↦ m > prev ∧ u m ∈ Bₒ x (1/(n + 1))
      let dec := Classical.decPred p; apply And.right
      apply Nat.find_spec (p := p)
     intro V hV
     rcases hV with ⟨Vo, ⟨hxVo, houv, hVoV⟩⟩
     specialize houv x hxVo
     rcases houv with ⟨r, ⟨hr_pos, hB⟩⟩
     have inegB : ∃ N : ℕ, ∀ n ≥ N, d((1/(n+1) : ℝ), 0) ≤ r := by apply conv_of_inv r hr_pos
     rcases inegB with ⟨m , hm⟩
     use m + 1
     intro n hnm
     have n_pos : n > 0 := by linarith
     have le_n_pred : m ≤ n.pred := by
      apply Nat.le_pred_of_lt; exact Nat.lt_of_succ_le hnm
     rw[<-Nat.succ_pred_eq_of_pos n_pos, Nat.succ_eq_add_one]
     refold_let φ
     specialize inegφ n.pred
     specialize hm n.pred le_n_pred
     suffices h : u (φ (n.pred + 1)) ∈ Bₒ x r by
      exact hVoV (hB h)
     apply lt_of_lt_of_le inegφ
     dsimp [instEspaceMetriqueReal] at hm
     rwa [sub_zero, abs_of_pos] at hm; field_simp; linarith
--
 · intro hφ
   rcases hφ with ⟨φ, ⟨hexφ, hconv⟩⟩
   unfold val_adh
   intro V hV m
   unfold converge_vers at hconv
   specialize hconv V hV
   rcases hconv with ⟨l, hl⟩
   have h_infini : ∃ N : ℕ, ∀ k ≥ N, φ k ≥ m := extr_conv_infini hexφ m
   rcases h_infini with ⟨N, hN⟩
   specialize hl (max N l)
   have hmaxNL : max N l ≥ l := Nat.le_max_right N l
   have huφ : (u ∘ φ) (max N l) ∈ V := mem_preimage.mp (hl hmaxNL)
   use φ (max N l)
   constructor
   · apply hN (max N l) (Nat.le_max_left N l)
   · dsimp at huφ; exact huφ


lemma in_inv_vois (k : ℕ) {X : Type*} [EspaceMetrique X] (A : Partie X) (x : X)
  (h : x ∈ adh A) : ∃ a ∈ A, a ∈ Bₒ x (1/(k+1)) := by
  have est_vois_B : est_vois x (Bₒ x (1/(k+1))) := by
    apply ouv_est_vois
    · exact ouv_of_boule_ouv x (1/(k+1))
    · exact centre_in_boule x (by field_simp; linarith)
  specialize h (Bₒ x (1/(k+1))) est_vois_B
  rw [nonempty_def] at h
  rcases h with ⟨x1, hx1⟩; use x1; rwa [And.comm]

noncomputable def construction_adh {X : Type*} [EspaceMetrique X]
  (A : Partie X) (x : X) (h : x ∈ adh A) : ℕ → X
  | k => Exists.choose (in_inv_vois k A x h)

theorem in_adh_suite {X : Type*} [EspaceMetrique X] (A : Partie X) (x : X) : x ∈ adh A ↔
  ∃(u : ℕ → X), (∀n, u n ∈ A) ∧ (converge_vers u x) := by
  constructor
  · intro hxadh
    let u := construction_adh A x hxadh
    use u
    constructor
    · intro n; let spec := in_inv_vois n A x hxadh
      apply And.left; apply Exists.choose_spec spec
    · unfold converge_vers
      have inegφ : ∀ n : ℕ, d(u n, x) < 1/(n+1):= by
        intro n; change u n ∈ Bₒ x (1/(n + 1))
        let spec := in_inv_vois n A x hxadh
        apply And.right; apply Exists.choose_spec spec
      intro V hV
      rcases hV with ⟨Vo, ⟨hxVo, houv, hVoV⟩⟩
      specialize houv x hxVo
      rcases houv with ⟨r, ⟨hr_pos, hB⟩⟩
      have inegB : ∃ N : ℕ, ∀ n ≥ N, d((1/(n+1) : ℝ), 0) ≤ r := by apply conv_of_inv r hr_pos
      rcases inegB with ⟨m , hm⟩
      use m
      intro n hnm
      specialize inegφ n
      specialize hm n hnm
      suffices h : u n ∈ Bₒ x r by exact hVoV (hB h)
      apply lt_of_lt_of_le inegφ
      dsimp [instEspaceMetriqueReal] at hm
      rwa [sub_zero, abs_of_pos] at hm; field_simp; linarith
  · intro h V hV
    rcases h with ⟨u, ⟨hu_in_a, hconv_u_x⟩⟩
    unfold converge_vers at hconv_u_x
    specialize hconv_u_x V hV
    rcases hconv_u_x with ⟨n , hn⟩
    specialize hn n (Nat.le_refl n)
    specialize hu_in_a n
    apply inter_nonempty.mpr
    use u n

end EspTop
