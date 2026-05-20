import TopoTER.Chapitre5

open TER Set EspTop

-- 6. Espaces topologiques compacts

variable {X : Type*} [EspSepareT2 X]

-- 6.1. Compacité via les recouvrements

-- a)

@[simp] def couvrement (F : Familleₓ X) (A : Partie X) := A ⊆ ⋃ᵢ F

@[simp] def sous_couvrement (F : Familleₓ X) (J : Set F.ι) (A : Partie X) :=
  couvrement (SousFamille F J) A

class EspCompact (X : Type*) [EspSepareT2 X] where
  compact : ∀ C : Familleₓ X, (∀ A ∈ C, est_ouvert A) → couvrement C Ω →
    ∃ J, J.Finite ∧ sous_couvrement C J Ω

-- b)

def est_compact_f (X : Type*) [EspSepareT2 X] := ∀ F : Familleₓ X, (∀ A ∈ F,
  est_ferme A) → ⋂ᵢ F = ∅ → ∃ J, J.Finite ∧ ⋂ᵢ (SousFamille F J) = ∅

lemma comp_f_of_comp [C : EspCompact X] : est_compact_f X := by
  intro F h₁ h₂
  have F_ouvert : ∀ A ∈ F`ᶜ, est_ouvert A := by
    intro A hA; rw [est_ouvert_iff_compl_est_ferme]
    rw [in_compl_famille] at hA; exact h₁ Aᶜ hA
  have F_couvre : couvrement F`ᶜ Ω := by
    simp [←inter_famille_compl, h₂]
--
  rcases C.compact F`ᶜ F_ouvert F_couvre with ⟨J, hJ, J_couvre⟩
  use J, hJ; dsimp at J_couvre
  rw [←compl_of_sous_famille, ←inter_famille_compl] at J_couvre
  rwa [univ_subset_iff, compl_univ_iff] at J_couvre

instance {X : Type*} [EspSepareT2 X] {h : est_compact_f X} : EspCompact X
  where compact := by {
    intro F h₁ h₂
    have F_ferme : ∀ A ∈ F`ᶜ, est_ferme A := by
      intro A hA; rw [est_ferme]
      rw [in_compl_famille] at hA; exact h₁ Aᶜ hA
    have F_inter : ⋂ᵢ F`ᶜ = ∅ := by
      simp_all [←union_famille_compl]
--
    rcases h F`ᶜ F_ferme F_inter with ⟨J, hJ, J_inter⟩; use J, hJ
    rw [←compl_of_sous_famille, ←union_famille_compl] at J_inter
    dsimp; rwa [univ_subset_iff, ←compl_empty_iff]
  }

-- 6.2.

def est_compact (A : Partie X) := ∀ C : Famille X, (∀ P ∈ C, est_ouvert P)
  → couvrement C A → ∃ J, J.Finite ∧ sous_couvrement C J A

-- Théorème 6.4.

-- a)

-- b)

theorem compact_of_ferme [EspCompact X] {A : Partie X} (h : est_ferme A)
  : est_compact A := by sorry

-- Théorème 6.5.

theorem comp_of_continu_image {X Y : Type*} [EspSepareT2 X] [EspSepareT2 Y]
  {f : X → Y} (h : est_continu f) (A : Partie X) (comp : est_compact A) :
  est_compact (f '' A) := by sorry
--  intro C h₁ h₂
--  let F : Famille X := ⟨C.ι, i ↦ f ⁻¹' (C.u i)⟩
--  have F_couvre : couvrement F A := by
--    unfold couvrement; intro x x_in; unfold F
--    simp only [mem_iUnion, exists_prop, mem_preimage]
--    have in_image : f x ∈ f '' A := by use x
--    apply h₂ at in_image
--    simp_all only [mem_iUnion, exists_prop]
--
--  have F_ouvert : ∀ i ∈ F.I, est_ouvert (F.u i) := by
--    intro i hi; rw [continu_iff_preim_ouv] at h
--    apply h; exact h₁ i hi
--  rcases comp F F_ouvert F_couvre with ⟨J, J_sub, hJ⟩
--  use J, J_sub; intro y y_in; rw [mem_image] at y_in
--  rcases y_in with ⟨x, x_in, hx⟩; apply hJ at x_in
--  simp_all only [mem_iUnion, exists_prop]
--  rcases x_in with ⟨j, j_in, hj⟩; use j, j_in; rwa [←hx]

-- 6.2. Espaces métriques compacts

open Metrique

variable {E F : Type*} [M₁ : EspaceMetrique E] [M₂ : EspaceMetrique F]

theorem bornee_of_compact [Cmp : EspCompact E] : bornee E := by
  let C : Famille E := ⟨E, x ↦ Bₒ x 1⟩
  have C_ouvert : ∀ A ∈ C, est_ouvert A := by
    intro A hA; rcases hA with ⟨x, hx⟩
    dsimp [C] at hx; rw [←hx]; unfold est_ouvert;
    exact ouv_of_boule_ouv x 1
  have C_couvre : couvrement C Ω := by
    intro x hx; rw [mem_union_famille]; use Bₒ x 1, (by use x)
    exact centre_in_boule x zero_lt_one
--
  rcases Cmp.compact C C_ouvert C_couvre with ⟨J, hJ, J_couvre⟩
  let S := {d(x, y) | (x ∈ J) (y ∈ J)}
  have bdd : BddAbove S := by
    let f : C.ι × C.ι → ℝ := I ↦ d(I.1, I.2)
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

open Valuation VectorSpace EspaceNorme

variable {K E : Type*} [ValuationField K] [GroupeNorme E] [V : EspaceVecNorme K E]

open EspaceNorme in
lemma norme_lipschitz : lipschitz 1 N(K, E) := by
  intro x y; unfold instEspaceMetriqueReal
  dsimp; rw [one_mul, abs_sub_le_iff];
  apply And.intro
  · apply sub_ineq V.is_norm
  · unfold instEspaceMetriqueEspaceMetNorme; dsimp
    rw [norm_symm V.is_norm]; apply sub_ineq V.is_norm

-- 6.4. Compacts d'un e.v.n. de dimension finie

open Valuation VectorSpace K_n EspaceNorme

variable {n : ℕ} {K : Type*} [ValuationField K]

-- Lemme 6.23.

open EspaceNorme in
lemma norme_Kn_lipschitz {N : K ^ n → ℝ} (h : estNorme (K := K) N) :
  k_lipschitz N := by
  let e (i : Fin n) := canonBasis K i
  let C := sSup {N (e i) | i}
  use n * C; intro x y
  have ineq₁ : |N x - N y| ≤ N (x - y) := by
    rw [abs_sub_le_iff]; apply And.intro
    · apply sub_ineq h
    · rw [norm_symm h]; apply sub_ineq h
  apply le_trans ineq₁
--
  let z := x - y; refold_let z
  have ineq₂ : N z ≤ ∑ i, N (z.p i • e i) := by
    nth_rw 1 [inCanonBasis z]; induction n
    · case zero => simp [norm_zero h]
    · case succ k hk => apply Finset.le_sum_of_subadditive
                        · rw [norm_zero h]
                        · intro x y; apply h.ineq
  apply le_trans ineq₂; rw [mul_assoc, ←nsmul_eq_mul]
  nth_rw 10 [←Finset.card_fin n]
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
