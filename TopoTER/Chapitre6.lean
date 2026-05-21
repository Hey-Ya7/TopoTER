import TopoTER.Chapitre5

open TER Set EspTop

-- 6. Espaces topologiques compacts

variable {ι X Y : Type*} [EspTop X] [EspTop Y] [EspSepareT2 X] [EspSepareT2 Y]

-- 6.1. Compacité via les recouvrements

open Famille

-- a)

@[simp] def couvrement (F : Famille ι X) (A : Partie X) := A ⊆ ⋃ᵢ F

@[simp] def sous_couvrement (F : Famille ι X) (J : Set ι) (A : Partie X) :=
  couvrement (SousFamille F J) A

class EspCompact (X : Type*) [EspTop X] [EspSepareT2 X] where
  compact : ∀ ι : Type*, ∀ C : Famille ι X, (∀ A ∈ C, est_ouvert A) →
    couvrement C Ω → ∃ J, J.Finite ∧ sous_couvrement C J Ω

-- b)

def est_compact_f (X : Type*) [EspTop X] [EspSepareT2 X] := ∀ ι : Type*,
  ∀ F : Famille ι X, (∀ A ∈ F, est_ferme A) → ⋂ᵢ F = ∅ → ∃ J, J.Finite ∧
  ⋂ᵢ (SousFamille F J) = ∅

lemma comp_f_of_comp [C : EspCompact.{_, u} X] : est_compact_f.{_, u} X := by
  intro ι F h₁ h₂
  have F_ouvert : ∀ A ∈ F`ᶜ, est_ouvert A := by
    intro A hA; rw [est_ouvert_iff_compl_est_ferme]
    rw [in_compl_famille] at hA; exact h₁ Aᶜ hA
  have F_couvre : couvrement F`ᶜ Ω := by
    simp [←inter_famille_compl, h₂]
--
  rcases C.compact ι F`ᶜ F_ouvert F_couvre with ⟨J, hJ, J_couvre⟩
  use J, hJ; dsimp at J_couvre
  rw [←compl_of_sous_famille, ←inter_famille_compl] at J_couvre
  rwa [univ_subset_iff, compl_univ_iff] at J_couvre

instance {h : est_compact_f.{_, u} X} : EspCompact.{_, u} X
  where compact := by {
    intro ι F h₁ h₂
    have F_ferme : ∀ A ∈ F`ᶜ, est_ferme A := by
      intro A hA; rw [est_ferme]
      rw [in_compl_famille] at hA; exact h₁ Aᶜ hA
    have F_inter : ⋂ᵢ F`ᶜ = ∅ := by
      simp_all [←union_famille_compl]
--
    rcases h ι F`ᶜ F_ferme F_inter with ⟨J, hJ, J_inter⟩; use J, hJ
    rw [←compl_of_sous_famille, ←union_famille_compl] at J_inter
    dsimp; rwa [univ_subset_iff, ←compl_empty_iff]
  }

-- 6.2.

def est_compact (A : Partie X) := ∀ ι : Type*, ∀ C : Famille ι X, (∀ P ∈ C,
  est_ouvert P) → couvrement C A → ∃ J, J.Finite ∧ sous_couvrement C J A

-- Théorème 6.4.

-- a)

theorem ferme_of_compact {A : Partie X} (h : est_compact.{_, u_2} A) :
  est_ferme A := by
  rw [est_ferme, ouvert_ssi_vois]; intro x hx
  have sep_y : ∀ y ∈ A, ∃ U V, est_ouvert U ∧ est_ouvert V ∧ y ∈ U ∧ x ∈ V
    ∧ U ∩ V = ∅ := by
    intro y hy; expose_names; apply inst_1.est_separe y x
    intro eq; rw [eq] at hy; exact hx hy
  choose! u v hu hv y_in x_in disj using sep_y
--
  let F : Famille A X := ⟨y ↦ u y⟩
  have F_ouvert : ∀ P ∈ F, est_ouvert P := by
    intro P hP; rcases hP with ⟨y, hy⟩
    rw [←hy]; exact hu y y.prop
  have F_couvre : couvrement F A := by
    intro y hy; rw [mem_union_famille]
    use u y, (by use ⟨y, hy⟩); exact y_in y hy
  rcases h A F F_ouvert F_couvre with ⟨J, hJ, J_couvre⟩
--
  let V' := ⋂ j ∈ J, v j; use V'; constructor
  · simp only [V', mem_iInter]; intro j hj
    exact x_in j j.prop
  · unfold V'; apply inter_fini_ouvert (hI := hJ)
    intro j hj; exact hv j j.prop
  · intro z hz in_A; rcases J_couvre in_A with ⟨j, hj, z_in⟩
    rcases hj with ⟨y, hy⟩; dsimp [SousFamille] at y hy
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
theorem comp_of_continu_image {f : X → Y} (h : est_continu f) {A : Partie X}
  (comp : est_compact.{_, u} A) : est_compact.{_, u} (f '' A) := by
  intro ι C h₁ h₂
  let F : Famille ι X := ⟨i ↦ f ⁻¹' (C.u i)⟩
  have F_ouvert : ∀ A ∈ F, est_ouvert A := by
    intro A hA; rcases hA with ⟨i, hi⟩; dsimp [F] at hi
    rw [continu_iff_preim_ouv] at h; rw [←hi]
    apply h; apply h₁; use i
  have F_couvre : couvrement F A := by
    intro x x_in; rw [mem_union_famille]
    have in_image : f x ∈ f '' A := by use x
    apply h₂ at in_image; rcases in_image with ⟨B, hB, fx_in⟩
    use f ⁻¹' B; apply And.intro _ fx_in
    rcases hB with ⟨i, hi⟩; use i; simp [F, hi]
--
  rcases comp ι F F_ouvert F_couvre with ⟨J, hJ, J_couvre⟩
  use J, hJ; intro y y_in; rcases y_in with ⟨x, x_in, hx⟩
  apply J_couvre at x_in; rcases x_in with ⟨s, s_in, hs⟩
  rcases s_in with ⟨i, hi⟩; dsimp [SousFamille]; rw [←hi] at hs
  rw [mem_union_famille]; use C.u i, (by use i), (by rwa [←hx])

-- 6.2. Espaces métriques compacts

open Metrique

variable {E F : Type*} [M₁ : EspaceMetrique E] [M₂ : EspaceMetrique F]

theorem bornee_of_compact [Cmp : EspCompact.{_, u_4} E] : bornee E := by
  let C : Famille E E := ⟨x ↦ Bₒ x 1⟩
  have C_ouvert : ∀ A ∈ C, est_ouvert A := by
    intro A hA; rcases hA with ⟨x, hx⟩
    dsimp [C] at hx; rw [←hx]; unfold est_ouvert;
    exact ouv_of_boule_ouv x 1
  have C_couvre : couvrement C Ω := by
    intro x hx; rw [mem_union_famille]; use Bₒ x 1, (by use x)
    exact centre_in_boule x zero_lt_one
--
  rcases Cmp.compact E C C_ouvert C_couvre with ⟨J, hJ, J_couvre⟩
  let S := {d(x, y) | (x ∈ J) (y ∈ J)}
  have bdd : BddAbove S := by
    let f : E × E → ℝ := I ↦ d(I.1, I.2)
    apply Set.Finite.bddAbove
    apply Set.Finite.of_surjOn f (s := J ×ˢ J)
    · intro s hs; rcases hs with ⟨x, hx, y, hy, hs⟩
      use (x, y), (mem_prod.mp ⟨hx, hy⟩), hs
    · exact Set.Finite.prod hJ hJ
  rcases bdd with ⟨M, hM⟩; unfold bornee
  rw [←bdd_iff_bdd_by_nneg]; use M + 2; intro x hx y hy
--
  rcases J_couvre hx with ⟨A, hA, x_in⟩; rcases hA with ⟨i, hi⟩
  rcases J_couvre hy with ⟨B, hB, y_in⟩; rcases hB with ⟨j, hj⟩
  dsimp [SousFamille, C] at hi; dsimp [SousFamille, C] at hj
  have ineq₁ := M₁.is_dist.ineq x i.val y
  have ineq₂ := M₁.is_dist.ineq i.val j.val y
  have d_ij_in : d(i.val, j.val) ∈ S := by
    use i.val, i.prop, j.val, j.prop
  have ineq₃ := hM d_ij_in
  rw [←hi] at x_in; dsimp at x_in; rw [←hj] at y_in
  dsimp at y_in; rw [M₁.is_dist.symm] at y_in; linarith

-- 6.4. Compacts d'un e.v.n. de dimension finie

open Valuation VectorSpace K_n EspaceNorme

variable {n : ℕ} {K : Type*} [ValuationField K]

-- Lemme 6.23.

open EspaceNorme in
lemma norme_Kn_lipschitz {N : K ^ n → ℝ} (h : estNorme (K := K) N) :
  k_lipschitz N := by
  let e (i : Fin n) := canonBasis K i
  cases n
  · case zero => use 1, zero_lt_one; intro x y
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
