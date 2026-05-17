import TopoTER.Chapitre5

open TER Set EspTop

-- 6. Espaces topologiques compacts

variable {X : Type*} [EspSepareT2 X]

-- 6.1. Compacité via les recouvrements

-- a)

def couvrement (F : Famille X) (A : Partie X) := A ⊆ ⋃ᵢ F

def sous_couvrement (F : Famille X) (J : Set F.ι) (A : Partie X) :=
  couvrement ⟨J, i ↦ F.u i.val⟩ A

class EspCompact (X : Type*) extends EspSepareT2 X where
  compact := ∀ C : Famille X, (∀ i, est_ouvert (C.u i)) →
    couvrement C Ω → ∃ J, sous_couvrement C J Ω

-- 6.2.

def est_compact (A : Partie X) := ∀ C : Famille X, (∀ i, est_ouvert (C.u i))
  → couvrement C A → ∃ J, sous_couvrement C J A

-- Théorème 6.5.

theorem comp_of_continu_image {X Y : Type*} [EspSepareT2 X] [EspSepareT2 Y]
  {f : X → Y} (h : est_continu f) (A : Partie X) (comp : est_compact A) :
  est_compact (f '' A) := by
  intro C h₁ h₂
  let F : Famille X := ⟨C.ι, i ↦ f ⁻¹' (C.u i)⟩
  have F_couvre : couvrement F A := by
    unfold couvrement; intro x x_in; unfold F
    simp only [mem_iUnion, exists_prop, mem_preimage]
    have in_image : f x ∈ f '' A := by use x
    apply h₂ at in_image
    simp_all only [mem_iUnion, exists_prop]
--
  have F_ouvert : ∀ i ∈ F.I, est_ouvert (F.u i) := by
    intro i hi; rw [continu_iff_preim_ouv] at h
    apply h; exact h₁ i hi
  rcases comp F F_ouvert F_couvre with ⟨J, J_sub, hJ⟩
  use J, J_sub; intro y y_in; rw [mem_image] at y_in
  rcases y_in with ⟨x, x_in, hx⟩; apply hJ at x_in
  simp_all only [mem_iUnion, exists_prop]
  rcases x_in with ⟨j, j_in, hj⟩; use j, j_in; rwa [←hx]

open Metrique

variable {X Y : Type*} [EspaceMetrique X] [EspaceMetrique Y]

def lipschitz (k : ℝ) (f : X → Y) := ∀ x y, d(f x, f y) ≤ k * d(x, y)

def k_lipschitz (f : X → Y) := ∃ k, lipschitz k f

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
