import TopoTER.Préliminaires

open TER

-- 1. Espaces métriques

namespace Metrique

-- 1.1. Définition, premiers exemples

-- Définition 1.1.

variable {α : Type*} {X : Set α}

def nneg (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y ≥ 0

def sep (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y = 0 ↔ x = y

def symm (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y = d y x

def ineq (X : Set α) (d : α → α → ℝ) := ∀ x y z ∈ X, d x z ≤ d x y + d y z

structure estDistance (X : Set α) (d : α → α → ℝ) where
  nneg : nneg X d
  sep : sep X d
  symm : symm X d
  ineq : ineq X d

class EspaceMetrique (X : Set α) where
  d : α → α → ℝ
  is_dist : estDistance X d

notation X "(" x ", " y ")" => EspaceMetrique.d X x y

-- quelques lemmes élémentaires

variable [M : EspaceMetrique X]

lemma self_dist {x : α} (h : x ∈ X) : X(x, x) = 0 := by
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  rw [sep x h x h]

lemma sub_ineq : ∀ x y z ∈ X, X(x, y) - X(x, z) ≤ X(y, z) := by
  intro x hx y hy z hz; rw [sub_le_iff_le_add]
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  rw [symm x hx z hz, symm x hx y hy]; exact ineq y hy z hz x hx

-- Exemple 1.2.

-- 1.
@[simp] def abs_dist : ℝ → ℝ → ℝ := x ↦ y ↦ |x - y|

lemma abs_nneg : nneg R abs_dist := by
  intro x _ y _; apply abs_nonneg

lemma abs_sep : sep R abs_dist := by
  intro x _ y _; dsimp; rw [abs_eq_zero, sub_eq_zero]

lemma abs_symm : symm R abs_dist := by
  intro x _ y _; dsimp; rw [abs_sub_comm]

lemma abs_ineq : ineq R abs_dist := by
  intro x _ y _ z _; dsimp; apply abs_sub_le

instance : EspaceMetrique R where
  d := abs_dist
  is_dist := ⟨
    abs_nneg, abs_sep,
    abs_symm, abs_ineq
  ⟩

-- 2.
noncomputable section Complex
open Complex

@[simp] def module_dist : ℂ → ℂ → ℝ := x ↦ y ↦ ‖x - y‖ᵢ

lemma module_nneg : nneg C module_dist := by
  intro x _ y _; apply norm_nonneg

lemma module_sep : sep C module_dist := by
  intro x _ y _; dsimp; rw [norm_eq_zero, sub_eq_zero]

lemma module_symm : symm C module_dist := by
  intro x _ y _; dsimp; rw [norm_symm, neg_sub]

lemma module_ineq : ineq C module_dist := by
  intro x _ y _ z _; unfold module_dist
  have eq : x - z = (x - y) + (y - z) := by ring
  rw [eq]; apply norm_ineq

instance : EspaceMetrique C where
  d := module_dist
  is_dist := ⟨
    module_nneg, module_sep,
    module_symm, module_ineq
  ⟩

end Complex

-- 3.
noncomputable section Euclidean
open VectorSpace
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Euclidean E]

@[simp] def euclid_dist : E → E → ℝ := x ↦ y ↦ ‖x - y‖ₑ

lemma euclid_nneg : nneg E↑ euclid_dist := by
  intro x _ y _; apply norm_nonneg

lemma euclid_sep : sep E↑ euclid_dist := by
  intro x _ y _; dsimp; rw [norm_eq_zero, sub_eq_zero]

lemma euclid_symm : symm E↑ euclid_dist := by
  intro x _ y _; dsimp; rw [norm_symm, neg_sub]

lemma euclid_ineq : ineq E↑ euclid_dist := by
  intro x _ y _ z _; dsimp
  have eq : x - z = (x - y) + (y - z) := by abel
  rw [eq]; apply norm_ineq

instance : EspaceMetrique E↑ where
  d := euclid_dist
  is_dist := ⟨
    euclid_nneg, euclid_sep,
    euclid_symm, euclid_ineq
  ⟩

end Euclidean

-- 4.
noncomputable section Discrete
omit M
open Classical in
@[simp] def discrete_dist : α → α → ℝ := x ↦ y ↦ ite (x = y) 0 1

def Discrete (X : Set α) : Set α := X

lemma discrete_nneg : nneg X discrete_dist := by
  intro x _ y _; dsimp; split
  · case isTrue => rfl
  · case isFalse => linarith

lemma discrete_sep : sep X discrete_dist := by
  intro x _ y _; dsimp; split
  · case isTrue h => simp only [h]
  · case isFalse h => simp only [one_ne_zero, h]

lemma discrete_symm : symm X discrete_dist := by
  intro x _ y _; dsimp; rw [@Eq.comm α]

open Classical in
lemma discrete_ineq : ineq X discrete_dist := by
  intro x h1 y h2 z h3; dsimp; split
  · case isTrue => apply add_nonneg (discrete_nneg x h1 y h2)
                   apply discrete_nneg y h2 z h3
  · case isFalse h =>
    split
    · case isTrue h' =>
      have eq : ite (y = z) (0 : ℝ) 1 = 1 := by
        apply if_neg; rw [←h']; exact h
      rw [eq]; apply le_add_of_nonneg_left (le_refl 0)
    · case isFalse => apply le_add_of_nonneg_right
                      apply discrete_nneg y h2 z h3

instance {X : Set α} : EspaceMetrique (Discrete X) where
  d := discrete_dist
  is_dist := ⟨
    discrete_nneg, discrete_sep,
    discrete_symm, discrete_ineq
  ⟩

end Discrete

-- 5.

def Induite {A : Set α} (_ : A ⊆ X) : Set α := A

lemma induite_dist {A : Set α} (h : A ⊆ X) : estDistance A M.d := by
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩; constructor
  · case nneg => intro x hx y hy; apply nneg x (h hx) y (h hy)
  · case sep => intro x hx y hy; apply sep x (h hx) y (h hy)
  · case symm => intro x hx y hy; apply symm x (h hx) y (h hy)
  · case ineq => intro x hx y hy z hz; apply ineq x (h hx) y (h hy) z (h hz)

instance {A : Set α} {h : A ⊆ X} : EspaceMetrique (Induite h) where
  d := M.d
  is_dist := induite_dist h

end Metrique

-- Définition 1.3.

namespace EspaceNorme
open VectorSpace

variable {K : Type*} [Field K] [ValuationField K] {E : Type*} [AddCommGroup E]
  [Module K E]

def nneg (N : E → ℝ) := ∀ x, N x ≥ 0

def definie (N : E → ℝ) := ∀ x, N x = 0 ↔ x = 0

def homogen (N : E → ℝ) := ∀ x, ∀ a : K, N (a • x) = |a| * N x

def ineq (N : E → ℝ) := ∀ x y, N (x + y) ≤ N x + N y

class GroupeNorme (E : Type*) [AddCommGroup E] where
  norm : E → ℝ
  nneg : nneg norm
  definie : definie norm
  ineq : ineq norm

structure estNorme (N : E → ℝ) where
  nneg : nneg N
  definie : definie N
  homogen : homogen (K := K) N
  ineq : ineq N

notation : max "‖" x "‖" => GroupeNorme.norm x

class EspaceVecNorme (K : Type*) [Field K] [ValuationField K] (E : Type*)
  [AddCommGroup E] [G : GroupeNorme E] extends Module K E where
  norm : E → ℝ := G.norm
  homogen : homogen (K := K) G.norm

  is_norm : estNorme (K := K) G.norm :=
    ⟨G.nneg, G.definie, homogen, G.ineq⟩

-- Proposition 1.4.

open Metrique

theorem dist_of_norme (K : Type*) [Field K] [ValuationField K] (E : Type*)
  [AddCommGroup E] [GroupeNorme E] [V : EspaceVecNorme K E] :
  let d : E → E → ℝ := x ↦ y ↦ ‖x - y‖; estDistance E↑ d := by
  rcases V.is_norm with ⟨nneg, defi, homo, ineq⟩; constructor
  · case nneg => intro x _ y _; apply nneg
  · case sep => intro x _ y _; rw [defi, sub_eq_zero]
  · case symm => intro x _ y _; dsimp; rw [←neg_sub]
                 rw [←neg_one_smul K, homo, abs_neg_one, one_mul]
  · case ineq => intro x _ y _ z _; dsimp
                 have eq : x - z = (x - y) + (y - z) := by abel
                 rw [eq]; apply ineq

def MetriqueNorme (K : Type*) [Field K] [ValuationField K] (E : Type*)
  [AddCommGroup E] [GroupeNorme E] [EspaceVecNorme K E] : Set E := E↑

instance [G : GroupeNorme E] [EspaceVecNorme K E] : EspaceMetrique
  (MetriqueNorme K E) where
  d := x ↦ y ↦ ‖x - y‖
  is_dist := dist_of_norme K E

-- Proposition 1.5.

open R_n

def norme_sup {n : ℕ} : ℝ^n → ℝ := x ↦ ∑ i : Finset.range n, (x.p i)
instance {n : ℕ} : GroupeNorme ℝ^n where
  norm := norme_sup
  nneg := sorry
  definie := sorry
  ineq := sorry

end EspaceNorme

-- 1.2. Ouverts et fermés d'un espace métrique

-- Définition 1.6.

open Metrique

variable {α : Type} {X : Set α} [M : EspaceMetrique X]

@[simp] def Metrique.EspaceMetrique.boule_ouverte (a : α) (r : ℝ) :=
  {x ∈ X | X(x, a) < r}

@[simp] def Metrique.EspaceMetrique.boule_fermee (a : α) (r : ℝ) :=
  {x ∈ X | X(x, a) ≤ r}

abbrev Metrique.EspaceMetrique.Bₒ (a : α) (r : ℝ) := M.boule_ouverte a r

abbrev Metrique.EspaceMetrique.Bf (a : α) (r : ℝ) := M.boule_fermee a r

@[simp] lemma boule_vide {a : α} {r : ℝ} (ha : a ∈ X) (hr : r ≤ 0) :
  M.Bₒ a r = ∅ := by
  suffices h : ∀ x ∈ X, r ≤ X(x, a) by simp_all
  intro x hx
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply le_trans hr (nneg x hx a ha)

@[simp] lemma boule_vide_f {a : α} {r : ℝ} (ha : a ∈ X) (hr : r < 0) :
  M.Bf a r = ∅ := by
  suffices h : ∀ x ∈ X, r < X(x, a) by simp_all
  intro x hx
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply lt_of_lt_of_le hr (nneg x hx a ha)

lemma centre_in_boule {a : α} {r : ℝ} (ha : a ∈ X) (hr : r > 0) :
  a ∈ M.Bₒ a r := by
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply And.intro ha; rw [self_dist ha]; linarith

-- Définition 1.7.

def Metrique.EspaceMetrique.ouverte (A : Set α) := ∀ x ∈ A, ∃ r > 0,
  M.Bₒ x r ⊆ A

def Metrique.EspaceMetrique.fermee (A : Set α) := M.ouverte (X \ A)

@[simp] lemma ouverte_def {A : Set α} : M.ouverte A ↔ ∀ x ∈ A, ∃ r > 0,
  M.Bₒ x r ⊆ A := by rfl

@[simp] lemma fermee_def {A} : M.fermee A ↔ M.ouverte (X \ A) := by rfl

-- Exemple 1.8.

-- a)

@[simp] theorem ouverte_of_uni : M.ouverte X := by
  intro x hx; use 1, zero_lt_one; simp

@[simp] theorem ouverte_of_vide : M.ouverte ∅ := by
  intro x hx; absurd hx; simp

@[simp] theorem fermee_of_vide : M.fermee ∅ := by
  rw [fermee_def, Set.diff_empty]; apply ouverte_of_uni

@[simp] theorem fermee_of_uni : M.fermee X := by
  rw [fermee_def, Set.diff_self]; apply ouverte_of_vide

-- Proposition 1.9.

-- a)

@[simp] theorem ouverte_of_union {ι : Type} {u : ι → Set α}
  (hu : ∀ i, M.ouverte (u i)) : M.ouverte (⋃ i, u i) := by
  intro x hx; rcases hx with ⟨A, hA, x_in⟩
  rcases hA with ⟨i, hi⟩; rw [←hi] at x_in
  rcases (hu i x x_in) with ⟨r, r_pos, hr⟩
  use r, r_pos; exact Set.subset_iUnion_of_subset i hr

-- b)

@[simp] theorem ouverte_of_inter {A B : Set α} (hA : M.ouverte A)
  (hB : M.ouverte B) : M.ouverte (A ∩ B) := by
  intro x hx; rw [Set.mem_inter_iff] at hx
  rcases hA x hx.left with ⟨r₁, r₁_pos, hr₁⟩
  rcases hB x hx.right with ⟨r₂, r₂_pos, hr₂⟩
--
  let r := min r₁ r₂
  have r_pos : r > 0 := by apply lt_min r₁_pos r₂_pos
  use r, r_pos; intro y hy; rw [Set.mem_inter_iff]
  apply And.intro
  · apply hr₁; dsimp; apply And.intro hy.left
    apply lt_of_lt_of_le hy.right; apply min_le_left
  · apply hr₂; dsimp; apply And.intro hy.left
    apply lt_of_lt_of_le hy.right; apply min_le_right

-- c)

@[simp] theorem ouv_of_boule_ouv {a : α} (h : a ∈ X) (r : ℝ) :
  M.ouverte (M.Bₒ a r) := by
  intro x hx; let r' := r - X(x, a)
  have r'_pos : r' > 0 := sub_pos_of_lt hx.right
  use r', r'_pos; intro y hy; dsimp
  apply And.intro hy.left; rw [←sub_add_cancel r (X(x, a))]
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply lt_of_le_of_lt (ineq y hy.left x hx.left a h)
  apply add_lt_add_left; exact hy.right

-- d)

theorem ouv_boule_union {U : Set α} (h : M.ouverte U) : ∃ ι : Type,
  ∃ u : ι → α × ℝ, U = ⋃ i, M.Bₒ (u i).fst (u i).snd := by
  let r (x : U) : ℝ := Exists.choose (h x.val x.prop)
  have r_prop : ∀ x, r x > 0 ∧ M.Bₒ x (r x) ⊆ U := by
    intro x; exact Exists.choose_spec (h x.val x.prop)
--
  use U, x ↦ (x.val, r x); rw [Set.ext_iff]; intro x
  apply Iff.intro
  case mp => intro in_u; let X : U := ⟨x, in_u⟩
             apply Set.mem_iUnion_of_mem X; sorry
  sorry

-- Definition 1.11.

def Metrique.EspaceMetrique.converges_to (u : ℕ → α) (l : α) := ∀ ε > 0,
  ∃ N, ∀ n ≥ N, X(u n, l) ≤ ε

def Metrique.EspaceMetrique.converges (u : ℕ → α) := ∃ l ∈ X,
  M.converges_to u l

-- Remarque 1.12.

def Metrique.EspaceMetrique.converges_to' (u : ℕ → α) (l : α) :=
  ∀ U, M.ouverte U → l ∈ U → ∃ N, ∀ n ≥ N, u n ∈ U

def seq_in (u : ℕ → α) (X : Set α) := ∀ n, u n ∈ X

theorem lim_iff_lim' {u : ℕ → α} (hu : seq_in u X) {l : α} (hl : l ∈ X) :
  M.converges_to u l ↔ M.converges_to' u l := by
  apply Iff.intro
  case mp => intro h U ouv l_in; have l_vois := ouv l l_in
             rcases l_vois with ⟨r, r_pos, hr⟩
             rcases (h (r/2) (by linarith)) with ⟨N, hN⟩
             use N; intro n hn; apply hr; apply And.intro (hu n)
             apply lt_of_le_of_lt (hN n hn); linarith
--
  case mpr => intro h' ε ε_pos; let U := M.Bₒ l ε
              have ouv_U := ouv_of_boule_ouv hl ε
              have l_in := centre_in_boule hl ε_pos
              rcases (h' U ouv_U l_in) with ⟨N, hN⟩
              use N; intro n hn; apply le_of_lt
              have u_n_in := hN n hn
              unfold U at u_n_in; apply u_n_in.right

-- Exemple 1.13.

-- a)

theorem conv_of_inv [M' : EspaceMetrique R] (u : ℕ → ℝ := n ↦ 1 / (n + 1)) :
  M'.converges_to u 0 := by
  intro ε ε_pos; sorry

-- 1.3. Espaces métriques complets (I)

-- Définition 1.14.

def Metrique.EspaceMetrique.cauchy (u : ℕ → α) := ∀ ε > 0, ∃ N, ∀ m ≥ N,
  ∀ n ≥ N, X(u m, u n) ≤ ε

-- Proposition 1.15.

-- a)

theorem cauchy_of_conv {u : ℕ → α} (hu : seq_in u X) (h : M.converges u) :
  M.cauchy u := by
  rcases h with ⟨l, l_in, hl⟩; intro ε ε_pos
  rcases (hl (ε / 2) (by linarith)) with ⟨N, hN⟩
  use N; intro m hm n hn
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  have ineq₁ := ineq (u m) (hu m) l l_in (u n) (hu n)
  have ineq₂ := hN m hm; have ineq₃ := hN n hn
  rw [symm l l_in (u n) (hu n)] at ineq₁; linarith

-- c)

def extraction (φ : ℕ → ℕ) := ∀ m n, m < n → φ m < φ n

lemma n_le_extr_n {φ : ℕ → ℕ} (h : extraction φ) : ∀ n, n ≤ φ n := by
  intro n; induction n
  · case zero => apply zero_le
  · case succ k hk => apply Nat.le_of_pred_lt; rw [Nat.pred_succ]
                      apply lt_of_le_of_lt hk; apply h; linarith

theorem conv_of_cauchy_extr {u : ℕ → α} (hu : seq_in u X) (h : M.cauchy u)
  (φ : ℕ → ℕ) (hφ : extraction φ) (conv : M.converges (u ∘ φ)) : M.converges u
  := by
  rcases conv with ⟨l, l_in, hl⟩; use l, l_in; intro ε ε_pos
  rcases (hl (ε / 2) (by linarith)) with ⟨N₁, hN₁⟩
  rcases (h (ε / 2) (by linarith)) with ⟨N₂, hN₂⟩
--
  let N := max N₁ N₂; use N; intro n hn
  have hn₁ := le_of_max_le_left hn
  have hn₂ := le_of_max_le_right hn
  have hn₃ := le_trans hn₂ (n_le_extr_n hφ n)
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  have ineq₁ := ineq (u n) (hu n) ((u ∘ φ) n) (hu (φ n)) l l_in
  have ineq₂ := hN₁ n hn₁; have ineq₃ := hN₂ n hn₂ (φ n) hn₃
  rw [Function.comp_apply] at ineq₁ ineq₂; linarith

-- Définition 1.16.

def complet (X : Set α) [M : EspaceMetrique X] := ∀ u, seq_in u X →
  M.cauchy u → M.converges u
