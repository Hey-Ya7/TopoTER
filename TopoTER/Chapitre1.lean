import TopoTER.Préliminaires

open TER

-- 1. Espaces métriques

namespace Metrique

-- 1.1. Définition, premiers exemples

-- Définition 1.1.

variable {α : Type*} {X : Set α}

def nneg (d : X → X → ℝ) := ∀ x y, d x y ≥ 0

def sep (d : X → X → ℝ) := ∀ x y, d x y = 0 ↔ x = y

def symm (d : X → X → ℝ) := ∀ x y, d x y = d y x

def ineq (d : X → X → ℝ) := ∀ x y z, d x z ≤ d x y + d y z

structure estDistance (d : X → X → ℝ) where
  nneg : nneg d
  sep : sep d
  symm : symm d
  ineq : ineq d

class EspaceMetrique (X : Set α) where
  d : X → X → ℝ
  is_dist : estDistance d

scoped syntax : max (name := dist) atomic("d(") term ", " term ")" : term
macro_rules (kind := dist)
  | `(d($x, $y)) => `(EspaceMetrique.d $x $y)

-- quelques lemmes élémentaires

variable [M : EspaceMetrique X]

lemma self_dist (x : X) : d(x, x) = 0 := by
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩; rw [sep]

lemma sub_ineq : ∀ x y z : X, d(x, y) - d(x, z) ≤ d(y, z) := by
  intro x y z; rw [sub_le_iff_le_add]
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  rw [symm x z, symm x y]; exact ineq y z x

-- Exemple 1.2.

-- 1.
@[simp] def abs_dist : R → R → ℝ := x ↦ y ↦ |x - y|

lemma abs_nneg : nneg abs_dist := by
  intro x y; apply abs_nonneg

lemma abs_sep : sep abs_dist := by
  intro x y; dsimp
  rw [abs_eq_zero, sub_eq_zero, Subtype.val_inj]

lemma abs_symm : symm abs_dist := by
  intro x y; dsimp; rw [abs_sub_comm]

lemma abs_ineq : ineq abs_dist := by
  intro x y z; dsimp; apply abs_sub_le

instance : EspaceMetrique R where
  d := abs_dist
  is_dist := ⟨
    abs_nneg, abs_sep,
    abs_symm, abs_ineq
  ⟩

-- 2.
noncomputable section Complex
open Complex

@[simp] def module_dist : C → C → ℝ := x ↦ y ↦ ‖x - y‖ᵢ

lemma module_nneg : nneg module_dist := by
  intro x y; apply norm_nonneg

lemma module_sep : sep module_dist := by
  intro x y; dsimp
  rw [norm_eq_zero, sub_eq_zero, Subtype.val_inj]

lemma module_symm : symm module_dist := by
  intro x y; dsimp; rw [norm_symm, neg_sub]

lemma module_ineq : ineq module_dist := by
  intro x y z; unfold module_dist
  have eq : x.val - z = (x - y) + (y - z) := by ring
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

@[simp] def euclid_dist : E↑ → E↑ → ℝ := x ↦ y ↦ ‖x.val - y‖ₑ

lemma euclid_nneg : nneg euclid_dist (α := E) := by
  intro x y; apply norm_nonneg

lemma euclid_sep : sep euclid_dist (α := E) := by
  intro x y; dsimp
  rw [norm_eq_zero, sub_eq_zero, Subtype.val_inj]

lemma euclid_symm : symm euclid_dist (α := E) := by
  intro x y; dsimp; rw [norm_symm, neg_sub]

lemma euclid_ineq : ineq euclid_dist (α := E) := by
  intro x y z; dsimp
  have eq : x.val - z = (x - y) + (y - z) := by abel
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
@[simp] def discrete_dist (X : Set α) : X → X → ℝ := x ↦ y ↦
  if x = y then 0 else 1

def Discrete (X : Set α) : Set α := X

lemma discrete_nneg (X : Set α) : nneg (discrete_dist X) := by
  intro x y; dsimp; split
  · case isTrue => rfl
  · case isFalse => linarith

lemma discrete_sep (X : Set α) : sep (discrete_dist X) := by
  intro x y; dsimp; split
  · case isTrue h => simp only [h]
  · case isFalse h => simp only [one_ne_zero, h]

lemma discrete_symm (X : Set α) : symm (discrete_dist X) := by
  intro x y; dsimp; congr 1; rw [Eq.comm (a := x)]

open Classical in
lemma discrete_ineq (X : Set α) : ineq (discrete_dist X) := by
  intro x y z; dsimp; split
  · case isTrue => apply add_nonneg (discrete_nneg X x y)
                   exact discrete_nneg X y z
  · case isFalse h =>
    split
    · case isTrue h' =>
      have eq : (if y = z then (0 : ℝ) else 1) = 1 := by
        apply if_neg; rw [←h']; exact h
      rw [eq]; apply le_add_of_nonneg_left (le_refl 0)
    · case isFalse => apply le_add_of_nonneg_right
                      exact discrete_nneg X y z

instance {X : Set α} : EspaceMetrique (Discrete X) where
  d := discrete_dist X
  is_dist := ⟨
    discrete_nneg X, discrete_sep X,
    discrete_symm X, discrete_ineq X
  ⟩

end Discrete

-- 5.

def Induite {A : Set α} (_ : A ⊆ X) : Set α := A
def induite_dist {A : Set α} (h : A ⊆ X) : A → A → ℝ := x ↦ y ↦
  d((⟨x, h x.prop⟩ : X), ⟨y, h y.prop⟩)

lemma dist_of_induite {A} (h : A ⊆ X) : estDistance (induite_dist h) := by
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩; constructor
  · case nneg => intro x y; unfold induite_dist; apply nneg
  · case sep => intro x y; unfold induite_dist
                rw [sep, Subtype.mk.injEq, Subtype.val_inj]
  · case symm => intro x y; unfold induite_dist; apply symm
  · case ineq => intro x y z; unfold induite_dist; apply ineq

instance {A : Set α} {h : A ⊆ X} : EspaceMetrique (Induite h) where
  d := induite_dist h
  is_dist := dist_of_induite h

end Metrique

-- Définition 1.3.

namespace EspaceNorme
open Valuation VectorSpace

variable {K : Type*} [Field K] [VF : ValuationField K] {E : Type*}
  [AddCommGroup E] [Module K E]

def nneg (N : E → ℝ) := ∀ x, N x ≥ 0

def definie (N : E → ℝ) := ∀ x, N x = 0 ↔ x = 0

def homogen (N : E → ℝ) := ∀ x, ∀ a : K, N (a • x) = |a|ₖ * N x

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
  let d : E↑ → E↑ → ℝ := x ↦ y ↦ ‖x.val - y‖; estDistance d := by
  rcases V.is_norm with ⟨nneg, defi, homo, ineq⟩; constructor
  · case nneg => intro x y; apply nneg
  · case sep => intro x y; rw [defi, sub_eq_zero, Subtype.val_inj]
  · case symm => intro x y; dsimp; rw [←neg_sub]
                 rw [←neg_one_smul K, homo, abs_neg_one, one_mul]
  · case ineq => intro x y z; dsimp
                 have eq : x.val - z = (x - y) + (y - z) := by abel
                 rw [eq]; apply ineq

def MetriqueNorme (K : Type*) [Field K] [ValuationField K] (E : Type*)
  [AddCommGroup E] [GroupeNorme E] [EspaceVecNorme K E] : Set E := E↑

instance [G : GroupeNorme E] [EspaceVecNorme K E] : EspaceMetrique
  (MetriqueNorme K E) where
  d := x ↦ y ↦ ‖x.val - y‖
  is_dist := dist_of_norme K E

-- Proposition 1.5.

open K_n
variable {n : ℕ}

noncomputable def norme_sup : K^n → ℝ := x ↦ sSup {|x.p i|ₖ | i}

@[simp] lemma norme_Kzero (x : K^(0 : ℕ)) : norme_sup x = 0 := by
  unfold norme_sup; simp

lemma Kn_nonempty {n : ℕ} (h : n > 0) (x : K^n) : let s := {|x.p i|ₖ | i};
  s.Nonempty := by use |x.p ⟨0, h⟩|ₖ, ⟨0, h⟩

open SupReal in
noncomputable instance : GroupeNorme K^n where
  norm := norme_sup
  nneg := by {
    intro x; apply Real.sSup_nonneg
    intro xi x_in; rcases x_in with ⟨i, hi⟩
    rw [←hi]; apply Valuation.abs_nonneg
  }

  definie := by {
    intro x; unfold norme_sup; rw [eq_zero_iff]
    apply Iff.intro
    · case mp => intro hi i; apply abs_le_zero
                 rw [←hi]; apply le_csSup
                 · apply bddabove_of_fin_image
                 · dsimp; use i
    · case mpr => intro h; cases n
                  · case zero => apply norme_Kzero
                  · case succ k =>
                    have h₁ := Nat.zero_lt_succ k
                    have h₂ := Kn_nonempty (K := K) h₁ x
                    apply sSup_const h₂; intro x x_in
                    rcases x_in with ⟨i, hi⟩; rw [h i] at hi
                    rw [←Valuation.abs_zero (K := K), hi]
  }

  ineq := by {
    intro x y; cases n
    · case zero => simp [norme_Kzero]
    · case succ k =>
        let sx := {|x.p i|ₖ | i}; let sy := {|y.p i|ₖ | i}
        let s := {|(x + y).p i|ₖ | i}; let s' := sx + sy
        have h := Nat.zero_lt_succ k
        have hx := Kn_nonempty (K := K) h x
        have hy := Kn_nonempty (K := K) h y
        have hs := Kn_nonempty (K := K) h (x + y)
        have hs' := add_nonempty hx hy
--
        have ineq₁ : sSup s ≤ sSup s' := by
          apply SupReal.sSup_le_sSup hs
          · apply add_bddabove
            repeat apply bddabove_of_fin_image
          · intro u u_in; rcases u_in with ⟨i, hi⟩
            have in_x : |x.p i|ₖ ∈ sx := by use i
            have in_y : |y.p i|ₖ ∈ sy := by use i
            use |x.p i|ₖ + |y.p i|ₖ; apply And.intro
            · case left => use ⟨|x.p i|ₖ, |y.p i|ₖ⟩, ⟨in_x, in_y⟩
            · case right => rw [←hi]; apply abs_add_ineq
        apply le_trans ineq₁; apply sSup_add_ineq hx _ hy _
        repeat apply bddabove_of_fin_image
  }

open Real in
noncomputable instance : EspaceVecNorme K K^n where
  homogen := by {
    intro x a
    suffices h : {|(a • x).p i|ₖ | i} = |a|ₖ • {|x.p i|ₖ | i} by
      dsimp [GroupeNorme.norm, norme_sup]; rw [←smul_eq_mul]
      rw [←sSup_smul_of_nonneg (abs_nonneg a), h]
    ext r; simp [HSMul.hSMul]
  }

def norme_inf : K^n → ℝ := x ↦ ∑ i, |x.p i|ₖ

def Inf (α : Type _) : Type _ := α
instance {E : Type*} [G : AddCommGroup E] : AddCommGroup (Inf E) := G
instance {K E : Type*} [Field K] [AddCommGroup E] [M : Module K E] :
  Module K (Inf E) := M

instance : GroupeNorme (Inf K^n) where
  norm := norme_inf
  nneg := by {
    intro x; apply Finset.sum_nonneg
    intro i hi; apply Valuation.abs_nonneg
  }

  definie := by {
    intro x; unfold norme_inf
    rw [Finset.sum_eq_zero_iff_of_nonneg, eq_zero_iff]
    · apply Iff.intro
      · case mp => intro hi i; rw [←abs_definie]
                   apply hi i; apply Finset.mem_univ
      · case mpr => intro hi i i_in; rw [abs_definie, hi i]
    · intro i hi; apply Valuation.abs_nonneg
  }

  ineq := by {
    intro x y; unfold norme_inf; rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i hi; apply abs_add_ineq
  }

open Real in
instance : EspaceVecNorme K (Inf K^n) where
  homogen := by {
    intro x a; dsimp [GroupeNorme.norm, norme_inf]
    rw [Finset.mul_sum]; congr; ext i; rw [abs_mul_homo]; rfl
  }

noncomputable def norme_euclid : K^n → ℝ := x ↦ √(∑ i, |x.p i|ₖ^2)
-- on réduit au cas simple ℝⁿ :
def Rn_of_Kn (x : K^n) : ℝ^n where
  p := i ↦ |x.p i|ₖ

lemma euclid_eq_Rn_norm (x : K^n) : norme_euclid x = ‖Rn_of_Kn x‖ₑ := by
  dsimp [norme_euclid, norm, Euclidean.scalar, Rn_prod]
  congr 2; dsimp [Rn_of_Kn]; ext; ring

def Eucl (α : Type _) : Type _ := α
instance {K : Type*} [G : AddCommGroup K] : AddCommGroup (Eucl K) := G
instance {K E : Type*} [Field K] [AddCommGroup E] [M : Module K E] :
  Module K (Eucl E) := M

open Real in
noncomputable instance : GroupeNorme (Eucl K^n) where
  norm := norme_euclid
  nneg := by intro x; apply sqrt_nonneg

  definie := by {
    intro x; rw [euclid_eq_Rn_norm, norm_eq_zero]
    rw [eq_zero_iff, eq_zero_iff]; dsimp [Rn_of_Kn]
    apply Iff.intro
    case mp => intro h i; rw [←abs_definie, h i]
    case mpr => intro h i; rw [abs_definie, h i]
  }

  ineq := by {
    intro x y; unfold norme_euclid
    let sx := ∑ i, |x.p i|ₖ ^ 2; let sy := ∑ i, |y.p i|ₖ ^ 2
    let s := ∑ i, |(x + y).p i|ₖ ^ 2
    have sum_nneg (k : K^n) : 0 ≤ ∑ i, |k.p i|ₖ ^ 2 :=
      by apply Finset.sum_nonneg; intro i h; apply sq_nonneg
    have x_add_y_nneg : 0 ≤ √sx + √sy := by
      apply add_nonneg; repeat apply sqrt_nonneg
--
    have ineq : ∑ i, |(x + y).p i|ₖ^2 ≤ ∑ i, |x.p i|ₖ^2 +
                ∑ i, 2 * (|x.p i|ₖ * |y.p i|ₖ) + ∑ i, |y.p i|ₖ^2 := by
      rw [←Finset.sum_add_distrib, ←Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro i _
      calc |(x + y).p i|ₖ^2
      _ = |(x + y).p i * (x + y).p i|ₖ := by simp [sq]
      _ = |(x.p i + y.p i) * (x.p i + y.p i)|ₖ := by congr
      _ = |(x.p i)^2 + 2 * x.p i * y.p i + (y.p i)^2|ₖ := by congr; ring
      _ ≤ |(x.p i)^2 + 2 * x.p i * y.p i|ₖ + |(y.p i)^2|ₖ := abs_add_ineq _ _
      _ ≤ |(x.p i)^2|ₖ + |2 * x.p i * y.p i|ₖ + |(y.p i)^2|ₖ := by {
        apply add_le_add_left; apply abs_add_ineq
      }
      _ ≤ |x.p i|ₖ^2 + |2 * x.p i * y.p i|ₖ + |y.p i|ₖ^2 := by simp
      _ ≤ _ := by {
        apply add_le_add_left; apply add_le_add_right
        rw [two_mul, two_mul, add_mul, abs_mul_homo]; apply abs_add_ineq
      }
--
    rw [←abs_of_nonneg (sqrt_nonneg s)]
    rw [←abs_of_nonneg x_add_y_nneg, ←sq_le_sq]
    rw [sq_sqrt (sum_nneg (x + y)), add_sq]
    rw [sq_sqrt (sum_nneg x), sq_sqrt (sum_nneg y)]
    apply le_trans ineq; apply add_le_add_left
    apply add_le_add_right; rw [mul_assoc, ←Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ zero_le_two
--
    unfold sx sy; rw [←norme_euclid, ←norme_euclid]
    let kx := Rn_of_Kn x; let ky := Rn_of_Kn y
    have eq : ∑ i, |x.p i|ₖ * |y.p i|ₖ = ⟨kx, ky⟩ := by rfl
    rw [eq, euclid_eq_Rn_norm, euclid_eq_Rn_norm]; apply cauchy_schwarz
  }

open Real in
noncomputable instance : EspaceVecNorme K (Eucl K^n) where
  homogen := by {
    intro x a; dsimp [GroupeNorme.norm, norme_euclid]
    rw [←sqrt_sq (Valuation.abs_nonneg a)]
    rw [←sqrt_mul (sq_nonneg |a|ₖ), Finset.mul_sum]
    congr; ext i; simp [sq, SMul.smul, instHSMul]; ring_nf
  }

end EspaceNorme

-- 1.2. Ouverts et fermés d'un espace métrique

-- Définition 1.6.

open Metrique

variable {α : Type} {X : Set α} [M : EspaceMetrique X]

@[simp] def boule_ouverte (a : X) (r : ℝ) := {x | d(x, a) < r}

@[simp] def boule_fermee (a : X) (r : ℝ) := {x | d(x, a) ≤ r}

abbrev Set.Bₒ (a : X) (r : ℝ) := boule_ouverte a r

abbrev Set.Bf (a : X) (r : ℝ) := boule_fermee a r

@[simp] lemma boule_vide (a) {r : ℝ} (hr : r ≤ 0) : X.Bₒ a r = ∅ := by
  suffices h : ∀ x, r ≤ d(x, a) by ext; simp_all
  intro x; rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply le_trans hr (nneg x a)

@[simp] lemma boule_vide_f (a) {r : ℝ} (hr : r < 0) : X.Bf a r = ∅ := by
  suffices h : ∀ x, r < d(x, a) by ext; simp_all
  intro x; rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply lt_of_lt_of_le hr (nneg x a)

lemma centre_in_boule (a : X) {r : ℝ} (hr : r > 0) : a ∈ X.Bₒ a r := by
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  dsimp; rw [self_dist a]; linarith

-- Définition 1.7.

def Set.ouverte (A : Set X) := ∀ x ∈ A, ∃ r > 0, X.Bₒ x r ⊆ A

def Set.fermee (A : Set X) := X.ouverte (Ω \ A)

@[simp] lemma ouverte_def (A : Set X) : X.ouverte A ↔ ∀ x ∈ A, ∃ r > 0,
  X.Bₒ x r ⊆ A := by rfl

@[simp] lemma fermee_def (A) : X.fermee A ↔ X.ouverte (Ω \ A) := by rfl

-- Exemple 1.8.

-- a)

@[simp] theorem ouverte_of_uni : X.ouverte Ω := by
  intro x hx; use 1, zero_lt_one; simp

@[simp] theorem ouverte_of_vide : X.ouverte ∅ := by
  intro x hx; absurd hx; simp

@[simp] theorem fermee_of_vide : X.fermee ∅ := by
  rw [fermee_def, Set.diff_empty]; apply ouverte_of_uni

@[simp] theorem fermee_of_uni : X.fermee Ω := by
  rw [fermee_def, Set.diff_self]; apply ouverte_of_vide

-- Proposition 1.9.

-- a)

@[simp] theorem ouverte_of_union {ι : Type} {u : ι → Set X}
  (hu : ∀ i, X.ouverte (u i)) : X.ouverte (⋃ i, u i) := by
  intro x hx; rcases hx with ⟨A, hA, x_in⟩
  rcases hA with ⟨i, hi⟩; rw [←hi] at x_in
  rcases (hu i x x_in) with ⟨r, r_pos, hr⟩
  use r, r_pos; exact Set.subset_iUnion_of_subset i hr

-- b)

@[simp] theorem ouverte_of_inter {A B : Set X} (hA : X.ouverte A)
  (hB : X.ouverte B) : X.ouverte (A ∩ B) := by
  intro x hx; rw [Set.mem_inter_iff] at hx
  rcases hA x hx.left with ⟨r₁, r₁_pos, hr₁⟩
  rcases hB x hx.right with ⟨r₂, r₂_pos, hr₂⟩
--
  let r := min r₁ r₂
  have r_pos : r > 0 := by apply lt_min r₁_pos r₂_pos
  use r, r_pos; intro y hy; rw [Set.mem_inter_iff]
  apply And.intro
  · apply hr₁; dsimp; apply lt_of_lt_of_le hy (min_le_left r₁ r₂)
  · apply hr₂; dsimp; apply lt_of_lt_of_le hy (min_le_right r₁ r₂)

-- c)

@[simp] theorem ouv_of_boule_ouv (a : X) (r : ℝ) : X.ouverte (X.Bₒ a r)
  := by
  intro x hx; let r' := r - d(x, a)
  have r'_pos : r' > 0 := sub_pos_of_lt hx
  use r', r'_pos; intro y hy; dsimp; rw [←sub_add_cancel r d(x, a)]
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply lt_of_le_of_lt (ineq y x a); apply add_lt_add_left; exact hy

-- d)

theorem ouv_boule_union {U : Set X} (h : X.ouverte U) : ∃ ι : Type,
  ∃ u : ι → X × ℝ, U = ⋃ i, X.Bₒ (u i).fst (u i).snd := by
  let r (x : U) : ℝ := Exists.choose (h x.val x.prop)
  have r_prop : ∀ x, r x > 0 ∧ X.Bₒ x (r x) ⊆ U := by
    intro x; exact Exists.choose_spec (h x.val x.prop)
--
  use U, x ↦ (x.val, r x); ext x; apply Iff.intro
  · case mp => intro in_u; let X : U := ⟨x, in_u⟩
               apply Set.mem_iUnion_of_mem X
               apply centre_in_boule; exact (r_prop X).left
  · case mpr => intro in_U; rcases in_U with ⟨U', hU', x_in⟩
                rcases hU' with ⟨U'', hU''⟩; dsimp at hU''
                apply (r_prop U'').right; rwa [←hU''] at x_in

-- Definition 1.11.

def Set.converges_to (u : ℕ → X) (l : X) := ∀ ε > 0, ∃ N, ∀ n ≥ N,
  d(u n, l) ≤ ε

def Set.converges (u : ℕ → X) := ∃ l, X.converges_to u l

-- Remarque 1.12.

def Set.converges_to' (u : ℕ → X) (l : X) := ∀ U, X.ouverte U → l ∈ U →
  ∃ N, ∀ n ≥ N, u n ∈ U

theorem lim_iff_lim' (u : ℕ → X) (l : X) : X.converges_to u l ↔
  X.converges_to' u l := by
  apply Iff.intro
  case mp => intro h U ouv l_in; have l_vois := ouv l l_in
             rcases l_vois with ⟨r, r_pos, hr⟩
             rcases (h (r/2) (by linarith)) with ⟨N, hN⟩
             use N; intro n hn; apply hr
             apply lt_of_le_of_lt (hN n hn); linarith
--
  case mpr => intro h' ε ε_pos; let U := X.Bₒ l ε
              have ouv_U := ouv_of_boule_ouv l ε
              have l_in := centre_in_boule l ε_pos
              rcases (h' U ouv_U l_in) with ⟨N, hN⟩
              use N; intro n hn; apply le_of_lt
              have u_n_in := hN n hn
              unfold U at u_n_in; apply u_n_in

-- Exemple 1.13.

-- a)

theorem conv_of_inv (u : ℕ → R := n ↦ ⟨1 / (n + 1), by simp⟩) :
  R.converges_to u (0 : ℝ) := by
  intro ε ε_pos; sorry

-- 1.3. Espaces métriques complets (I)

-- Définition 1.14.

def Set.cauchy (u : ℕ → X) := ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, d(u m, u n) ≤ ε

-- Proposition 1.15.

-- a)

theorem cauchy_of_conv (u : ℕ → X) (h : X.converges u) : X.cauchy u := by
  rcases h with ⟨l, hl⟩; intro ε ε_pos
  rcases (hl (ε / 2) (by linarith)) with ⟨N, hN⟩
  use N; intro m hm n hn
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  have ineq₁ := ineq (u m) l (u n)
  have ineq₂ := hN m hm; have ineq₃ := hN n hn
  rw [symm l (u n)] at ineq₁; linarith

-- c)

def extraction (φ : ℕ → ℕ) := ∀ m n, m < n → φ m < φ n

lemma n_le_extr_n {φ : ℕ → ℕ} (h : extraction φ) : ∀ n, n ≤ φ n := by
  intro n; induction n
  · case zero => apply zero_le
  · case succ k hk => apply Nat.le_of_pred_lt; rw [Nat.pred_succ]
                      apply lt_of_le_of_lt hk; apply h; linarith

theorem conv_of_cauchy_extr (u : ℕ → X) (h : X.cauchy u) (φ : ℕ → ℕ)
  (hφ : extraction φ) (conv : X.converges (u ∘ φ)) : X.converges u := by
  rcases conv with ⟨l, hl⟩; use l; intro ε ε_pos
  rcases (hl (ε / 2) (by linarith)) with ⟨N₁, hN₁⟩
  rcases (h (ε / 2) (by linarith)) with ⟨N₂, hN₂⟩
--
  let N := max N₁ N₂; use N; intro n hn
  have hn₁ := le_of_max_le_left hn
  have hn₂ := le_of_max_le_right hn
  have hn₃ := le_trans hn₂ (n_le_extr_n hφ n)
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  have ineq₁ := ineq (u n) ((u ∘ φ) n) l
  have ineq₂ := hN₁ n hn₁; have ineq₃ := hN₂ n hn₂ (φ n) hn₃
  rw [Function.comp_apply] at ineq₁ ineq₂; linarith

-- Définition 1.16.

def complet (X : Set α) [EspaceMetrique X] := ∀ u, X.cauchy u → X.converges u
