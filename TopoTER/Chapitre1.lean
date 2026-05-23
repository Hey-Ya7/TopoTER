import TopoTER.Préliminaires

open TER

-- 1. Espaces métriques

namespace Metrique

-- 1.1. Définition, premiers exemples

-- Définition 1.1.

variable {X : Type}

def nneg (d : X → X → ℝ) := ∀ x y, d x y ≥ 0

def sep (d : X → X → ℝ) := ∀ x y, d x y = 0 ↔ x = y

def symm (d : X → X → ℝ) := ∀ x y, d x y = d y x

def ineq (d : X → X → ℝ) := ∀ x y z, d x z ≤ d x y + d y z

structure estDistance (d : X → X → ℝ) where
  nneg : nneg d
  sep : sep d
  symm : symm d
  ineq : ineq d

class EspaceMetrique (X : Type) where
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
@[simp] def abs_dist : ℝ → ℝ → ℝ := x ↦ y ↦ |x - y|

lemma abs_nneg : nneg abs_dist := by
  intro x y; apply abs_nonneg

lemma abs_sep : sep abs_dist := by
  intro x y; dsimp; rw [abs_eq_zero, sub_eq_zero]

lemma abs_symm : symm abs_dist := by
  intro x y; dsimp; rw [abs_sub_comm]

lemma abs_ineq : ineq abs_dist := by
  intro x y z; dsimp; apply abs_sub_le

instance : EspaceMetrique ℝ where
  d := abs_dist
  is_dist := ⟨
    abs_nneg, abs_sep,
    abs_symm, abs_ineq
  ⟩

-- 2.
noncomputable section Complex
open Complex

@[simp] def module_dist : ℂ → ℂ → ℝ := x ↦ y ↦ ‖x - y‖ᵢ

lemma module_nneg : nneg module_dist := by
  intro x y; apply norm_nonneg

lemma module_sep : sep module_dist := by
  intro x y; dsimp; rw [norm_eq_zero, sub_eq_zero]

lemma module_symm : symm module_dist := by
  intro x y; dsimp; rw [norm_symm, neg_sub]

lemma module_ineq : ineq module_dist := by
  intro x y z; unfold module_dist
  have eq : x - z = (x - y) + (y - z) := by ring
  rw [eq]; apply norm_ineq

instance : EspaceMetrique ℂ where
  d := module_dist
  is_dist := ⟨
    module_nneg, module_sep,
    module_symm, module_ineq
  ⟩

end Complex

-- 3.
noncomputable section Euclidean
open VectorSpace
variable {E : Type} [AddCommGroup E] [Euclidean E]

@[simp] def euclid_dist : E → E → ℝ := x ↦ y ↦ ‖x - y‖ₑ

lemma euclid_nneg : nneg euclid_dist (X := E) := by
  intro x y; apply norm_nonneg

lemma euclid_sep : sep euclid_dist (X := E) := by
  intro x y; dsimp; rw [norm_eq_zero, sub_eq_zero]

lemma euclid_symm : symm euclid_dist (X := E) := by
  intro x y; dsimp; rw [norm_symm, neg_sub]

lemma euclid_ineq : ineq euclid_dist (X := E) := by
  intro x y z; dsimp
  have eq : x - z = (x - y) + (y - z) := by abel
  rw [eq]; apply norm_ineq

instance : EspaceMetrique E where
  d := euclid_dist
  is_dist := ⟨
    euclid_nneg, euclid_sep,
    euclid_symm, euclid_ineq
  ⟩

end Euclidean

-- 4.
noncomputable section Discrete
open Classical in
@[simp] def discrete_dist (X : Type) : X → X → ℝ := x ↦ y ↦
  if x = y then 0 else 1

def Discrete (X : Type) : Type _ := X

lemma discrete_nneg (X : Type) : nneg (discrete_dist X) := by
  intro x y; dsimp; split
  · case isTrue => rfl
  · case isFalse => linarith

lemma discrete_sep (X : Type) : sep (discrete_dist X) := by
  intro x y; dsimp; split
  · case isTrue h => simp only [h]
  · case isFalse h => simp only [one_ne_zero, h]

lemma discrete_symm (X : Type) : symm (discrete_dist X) := by
  intro x y; dsimp; congr 1; rw [Eq.comm (a := x)]

open Classical in
lemma discrete_ineq (X : Type) : ineq (discrete_dist X) := by
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

instance : EspaceMetrique (Discrete X) where
  d := discrete_dist X
  is_dist := ⟨
    discrete_nneg X, discrete_sep X,
    discrete_symm X, discrete_ineq X
  ⟩

end Discrete

-- 5.

def induite_dist (A : Partie X) : A → A → ℝ := x ↦ y ↦ d(x.val, y.val)

lemma dist_of_induite (A : Partie X) : estDistance (induite_dist A) := by
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩; constructor
  · case nneg => intro x y; unfold induite_dist; apply nneg
  · case sep => intro x y; unfold induite_dist
                rw [sep, Subtype.mk.injEq, Subtype.val_inj]
  · case symm => intro x y; unfold induite_dist; apply symm
  · case ineq => intro x y z; unfold induite_dist; apply ineq

variable {A : Partie X}

instance : EspaceMetrique (Induite A) where
  d := induite_dist A
  is_dist := dist_of_induite A

instance : Coe (Partie X) (Partie Induite A) where
  coe := S ↦ {x | (x : X) ∈ S}

omit M in
@[simp] lemma self_induite : (A : Partie Induite A) = Ω := by
  ext x; unfold Induite; simp

end Metrique

-- Définition 1.3.

namespace EspaceNorme
open Valuation VectorSpace

variable {K E : Type} [ValuationField K] [AddCommGroup E] [Module K E]

def nneg (N : E → ℝ) := ∀ x, N x ≥ 0

def definie (N : E → ℝ) := ∀ x, N x = 0 ↔ x = 0

def homogen (N : E → ℝ) := ∀ x, ∀ a : K, N (a • x) = |a|ₖ * N x

def ineq (N : E → ℝ) := ∀ x y, N (x + y) ≤ N x + N y

class GroupeNorme (E : Type) extends AddCommGroup E where
  norm : E → ℝ
  nneg : nneg norm
  definie : definie norm
  ineq : ineq norm

structure estNorme (N : E → ℝ) where
  nneg : nneg N
  definie : definie N
  homogen : homogen (K := K) N
  ineq : ineq N

lemma norm_zero {N : E → ℝ} (h : estNorme (K := K) N) : N 0 = 0 := by
  rw [h.definie]

lemma norm_neg {N : E → ℝ} (h : estNorme (K := K) N) : ∀ x, N (-x) = N x
  := by intro x; rw [←neg_one_smul K, h.homogen, abs_neg_one, one_mul]

lemma norm_symm {N : E → ℝ} (h : estNorme (K := K) N) : ∀ x y, N (x - y) =
  N (y - x) := by intro x y; rw [←neg_sub, norm_neg h]

lemma sub_ineq {N : E → ℝ} (h : estNorme (K := K) N) : ∀ x y, N x - N y ≤
  N (x - y) := by
  intro x y; rw [sub_le_iff_le_add]
  nth_rw 1 [←sub_add_cancel x y]; apply h.ineq

notation : max "‖" x "‖" => GroupeNorme.norm x

class EspaceVecNorme (K E : Type) [ValuationField K] [G : GroupeNorme E]
  extends Module K E where
  norm : E → ℝ := G.norm
  homogen : homogen (K := K) G.norm

  is_norm : estNorme (K := K) G.norm :=
    ⟨G.nneg, G.definie, homogen, G.ineq⟩

-- Proposition 1.4.

open Metrique

theorem dist_of_norme (K E : Type) [ValuationField K] [GroupeNorme E]
  [V : EspaceVecNorme K E] :
  let d : E → E → ℝ := x ↦ y ↦ ‖x - y‖; estDistance d := by
  rcases V.is_norm with ⟨nneg, defi, homo, ineq⟩; constructor
  · case nneg => intro x y; apply nneg
  · case sep => intro x y; rw [defi, sub_eq_zero]
  · case symm => intro x y; dsimp; rw [norm_symm V.is_norm]
  · case ineq => intro x y z; dsimp
                 have eq : x - z = (x - y) + (y - z) := by abel
                 rw [eq]; apply ineq

def EspaceMetNorme (K E : Type) [ValuationField K] [GroupeNorme E]
  [EspaceVecNorme K E] : Type _ := E

notation "Vec⟨" K " | " E "⟩" => EspaceMetNorme K E
notation "N(" K ", " E ")" => fun (x : Vec⟨K | E⟩) => ‖x‖

instance {K E : Type} [ValuationField K] [G : GroupeNorme E]
  [EspaceVecNorme K E] : GroupeNorme Vec⟨K | E⟩ := G

instance {K E : Type} [ValuationField K] [GroupeNorme E]
  [V : EspaceVecNorme K E] : EspaceVecNorme K Vec⟨K | E⟩ := V

instance {K E : Type} [ValuationField K] [GroupeNorme E]
  [EspaceVecNorme K E] : EspaceMetrique Vec⟨K | E⟩ where
  d := x ↦ y ↦ ‖x - y‖
  is_dist := dist_of_norme K E

-- Proposition 1.5.

open K_n
variable {n : ℕ}

noncomputable def norme_sup : K^n → ℝ := x ↦ sSup {|x.p i|ₖ | i}

@[simp] lemma norme_Kzero (x : K ^ (0 : ℕ)) : norme_sup x = 0 := by
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
    · case mpr =>
        intro h; cases n
        · case zero => apply norme_Kzero
        · case succ k =>
          have h' := Kn_nonempty (Nat.succ_pos k) x
          apply sSup_const h'; intro x x_in
          rcases x_in with ⟨i, hi⟩; rw [h i] at hi
          rw [←Valuation.abs_zero (K := K), hi]
  }

  ineq := by {
    intro x y; cases n
    · case zero => simp [norme_Kzero]
    · case succ k =>
        let sx := {|x.p i|ₖ | i}; let sy := {|y.p i|ₖ | i}
        let s := {|(x + y).p i|ₖ | i}; let s' := sx + sy
        have hx := Kn_nonempty (Nat.succ_pos k) x
        have hy := Kn_nonempty (Nat.succ_pos k) y
        have hs := Kn_nonempty (Nat.succ_pos k) (x + y)
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

noncomputable instance : EspaceMetrique K^n where
  d := x ↦ y ↦ ‖x - y‖
  is_dist := dist_of_norme K K^n

def norme_taxi : K^n → ℝ := x ↦ ∑ i, |x.p i|ₖ

@[simp] lemma norme_taxi_Kzero (x : K ^ (0 : ℕ)) : norme_taxi x = 0
  := by unfold norme_taxi; simp

def Inf (α : Type _) : Type _ := α
instance {E : Type} [G : AddCommGroup E] : AddCommGroup (Inf E) := G
instance {K E : Type} [Field K] [AddCommGroup E] [M : Module K E] :
  Module K (Inf E) := M

instance : GroupeNorme (Inf K^n) where
  norm := norme_taxi
  nneg := by {
    intro x; apply Finset.sum_nonneg
    intro i hi; apply Valuation.abs_nonneg
  }

  definie := by {
    intro x; unfold norme_taxi
    rw [Finset.sum_eq_zero_iff_of_nonneg, eq_zero_iff]
    · apply Iff.intro
      · case mp => intro hi i; rw [←abs_definie]
                   apply hi i; apply Finset.mem_univ
      · case mpr => intro hi i i_in; rw [abs_definie, hi i]
    · intro i hi; apply Valuation.abs_nonneg
  }

  ineq := by {
    intro x y; unfold norme_taxi; rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i hi; apply abs_add_ineq
  }

open Real in
instance : EspaceVecNorme K (Inf K^n) where
  homogen := by {
    intro x a; dsimp [GroupeNorme.norm, norme_taxi]
    rw [Finset.mul_sum]; congr; ext i; rw [abs_mul_homo]; rfl
  }

noncomputable def norme_euclid : K^n → ℝ := x ↦ √(∑ i, |x.p i|ₖ^2)
-- on réduit au cas simple ℝⁿ :
def Rn_of_Kn (x : K^n) : ℝ^n where
  p := i ↦ |x.p i|ₖ

@[simp] lemma norme_eucl_Kzero (x : K ^ (0 : ℕ)) : norme_euclid x = 0
  := by unfold norme_euclid; simp

lemma euclid_eq_Rn_norm (x : K^n) : norme_euclid x = ‖Rn_of_Kn x‖ₑ := by
  dsimp [norme_euclid, norm, Euclidean.scalar, Rn_prod]
  congr 2; dsimp [Rn_of_Kn]; ext; ring

def Eucl (α : Type _) : Type _ := α
instance {K : Type} [G : AddCommGroup K] : AddCommGroup (Eucl K) := G
instance {K E : Type} [Field K] [AddCommGroup E] [M : Module K E] :
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
    apply le_of_sq_le_sq _ (x_add_y_nneg)
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

structure NormeEquiv (E : Type) (norm₁ : E → ℝ) (norm₂ : E → ℝ) where
  exists_C : ∃ C > 0, ∀ x, norm₁ x ≤ C * norm₂ x
  exists_D : ∃ D > 0, ∀ x, norm₂ x ≤ D * norm₁ x

notation N₁ " ≃ " N₂ " on " E => NormeEquiv E N₁ N₂

instance NormeEq {E : Type} : Equivalence (NormeEquiv E) where
  refl := by {
    intro N; constructor
    · use 1, one_pos; simp
    · use 1, one_pos; simp
  }

  symm := by {
    intro N₁ N₂ h; rcases h with ⟨hC, hD⟩
    constructor
    · rcases hD with ⟨D, pos, h'⟩; use D
    · rcases hC with ⟨C, pos, h'⟩; use C
  }

  trans := by {
    intro N₁ N₂ N₃ h₁ h₂; rcases h₁ with ⟨hC₁, hD₁⟩
    rcases h₂ with ⟨hC₂, hD₂⟩; constructor
    · rcases hC₁ with ⟨C₁, pos₁, h'₁⟩
      rcases hC₂ with ⟨C₂, pos₂, h'₂⟩
      use C₁ * C₂, mul_pos pos₁ pos₂
      intro x; apply le_trans (h'₁ x)
      rw [mul_assoc, mul_le_mul_iff_right₀ pos₁]; apply h'₂
--
    · rcases hD₁ with ⟨D₁, pos₁, h'₁⟩
      rcases hD₂ with ⟨D₂, pos₂, h'₂⟩
      use D₂ * D₁, mul_pos pos₂ pos₁
      intro x; apply le_trans (h'₂ x)
      rw [mul_assoc, mul_le_mul_iff_right₀ pos₂]; apply h'₁
  }

lemma sup_equiv_taxi : norme_sup ≃ norme_taxi on K^n := by
  cases n
  · case zero => constructor
                 · use 1, one_pos; intro x; simp
                 · use 1, one_pos; intro x; simp
  · case succ k =>
    unfold norme_sup norme_taxi; constructor
    · use 1, one_pos; intro x; apply csSup_le
      · apply Kn_nonempty (Nat.succ_pos k)
      · intro b hb; rcases hb with ⟨i, hi⟩; rw [one_mul, ←hi]
        apply Finset.single_le_sum (f := i ↦ |x.p i|ₖ)
        · intro i hi; apply Valuation.abs_nonneg
        · apply Finset.mem_univ
--
    · use k.succ, (by apply Nat.cast_pos.mpr; simp)
      intro x; rw [←nsmul_eq_mul, ←Fin.sum_const]
      apply Finset.sum_le_sum; intro i hi
      apply le_csSup _ (by use i)
      apply SupReal.bddabove_of_fin_image

open Real in
lemma sup_equiv_eucl : norme_sup ≃ norme_euclid on K^n := by
  cases n
  · case zero => constructor
                 · use 1, one_pos; intro x; simp
                 · use 1, one_pos; intro x; simp
  · case succ k =>
    unfold norme_sup norme_euclid; constructor
    · use 1, one_pos; intro x; apply csSup_le
      · apply Kn_nonempty (Nat.succ_pos k)
      · intro b hb; rcases hb with ⟨i, hi⟩
        rw [one_mul, ←hi, le_sqrt (abs_nonneg (x.p i))]
        · apply Finset.single_le_sum (f := i ↦ |x.p i|ₖ ^ 2)
          · intro i hi; apply sq_nonneg
          · apply Finset.mem_univ
        · apply Finset.sum_nonneg; intro i hi; apply sq_nonneg
--
    · use √k.succ; apply And.intro
      · rw [gt_iff_lt, sqrt_pos, Nat.cast_pos]; simp
      intro x; apply le_of_sq_le_sq
      · nth_rw 2 [sq]; ring_nf; rw [sq_sqrt, sq_sqrt]
        · rw [←nsmul_eq_mul, ←Fin.sum_const]
          apply Finset.sum_le_sum; intro i hi; rw [sq_le_sq]
          apply abs_le_abs_of_nonneg (abs_nonneg (x.p i))
          apply le_csSup _ (by use i)
          apply SupReal.bddabove_of_fin_image
        · apply Nat.cast_nonneg
        · apply Finset.sum_nonneg; intro i hi; apply sq_nonneg
      · apply mul_nonneg (sqrt_nonneg k.succ); apply sSup_nonneg
        intro xi xi_in; rcases xi_in with ⟨i, hi⟩; rw [←hi]
        apply Valuation.abs_nonneg

lemma taxi_equiv_eucl : norme_taxi ≃ norme_euclid on K^n := by
  apply NormeEq.trans _ sup_equiv_eucl
  apply NormeEq.symm; exact sup_equiv_taxi

end EspaceNorme

-- 1.2. Ouverts et fermés d'un espace métrique

-- Définition 1.6.

open Metrique

variable {X : Type} [M : EspaceMetrique X]

@[simp] def boule_ouverte (a : X) (r : ℝ) := {x | d(x, a) < r}

@[simp] def boule_fermee (a : X) (r : ℝ) := {x | d(x, a) ≤ r}

abbrev Bₒ (a : X) (r : ℝ) := boule_ouverte a r

abbrev Bf (a : X) (r : ℝ) := boule_fermee a r

def is_boule (B : Partie X) := ∃ a, ∃ r, B = Bₒ a r

def is_boule_f (B : Partie X) := ∃ a, ∃ r, B = Bf a r

@[simp] lemma boule_vide (a : X) {r : ℝ} (hr : r ≤ 0) : Bₒ a r = ∅ := by
  suffices h : ∀ x, r ≤ d(x, a) by ext; simp_all
  intro x; rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply le_trans hr (nneg x a)

@[simp] lemma boule_vide_f (a : X) {r : ℝ} (hr : r < 0) : Bf a r = ∅ := by
  suffices h : ∀ x, r < d(x, a) by ext; simp_all
  intro x; rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply lt_of_lt_of_le hr (nneg x a)

lemma centre_in_boule (a : X) {r : ℝ} (hr : r > 0) : a ∈ Bₒ a r := by
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  dsimp; rw [self_dist a]; linarith

lemma boule_in_boule_f (a : X) {r : ℝ} (_ : r > 0) : Bₒ a r ⊆ Bf a r := by
  intro x x_in; dsimp; dsimp at x_in; linarith

lemma boule_in_boule_ge (a : X) {r R : ℝ} (_ : r > 0) (_ : R > 0) :
R ≥ r → Bₒ a r ⊆ Bₒ a R := by
  intro h x hx
  simp at *; linarith

lemma boule_in_boule_f_ge (a : X) {r R : ℝ} (_ : r > 0) (_ : R > 0) :
R ≥ r → Bₒ a r ⊆ Bf a R := by
  intro h x hx
  simp at *; linarith

lemma boule_f_in_boule_f_ge (a : X) {r R : ℝ} (_ : r > 0) (_ : R > 0) :
R ≥ r → Bf a r ⊆ Bf a R := by
  intro h x hx
  simp at *; linarith

lemma boule_f_in_boule_gt (a : X) {r R : ℝ} (_ : r > 0) (_ : R > 0) :
R > r → Bf a r ⊆ Bₒ a R := by
  intro h x hx
  simp at *; linarith

-- Définition 1.7.

def ouverte (A : Partie X) := ∀ x ∈ A, ∃ r > 0, Bₒ x r ⊆ A

def fermee (A : Partie X) := ouverte (Ω \ A)

@[simp] lemma ouverte_def (A : Partie X) : ouverte A ↔ ∀ x ∈ A, ∃ r > 0,
  Bₒ x r ⊆ A := by rfl

@[simp] lemma fermee_def (A : Partie X) : fermee A ↔ ouverte (Ω \ A) := by rfl

-- Exemple 1.8.

-- a)

@[simp] theorem ouverte_of_uni : ouverte (X := X) Ω := by
  intro x hx; use 1, one_pos; simp

@[simp] theorem ouverte_of_vide : ouverte (X := X) ∅ := by
  intro x hx; absurd hx; simp

@[simp] theorem fermee_of_vide : fermee (X := X) ∅ := by
  rw [fermee_def, Set.diff_empty]; apply ouverte_of_uni

@[simp] theorem fermee_of_uni : fermee (X := X) Ω := by
  rw [fermee_def, Set.diff_self]; apply ouverte_of_vide

abbrev Z_induite : Partie ℝ := Induite Z

lemma boule_in_Z_induite : ∀ x : Z_induite, Bₒ x (1/2) = {x} := by
  intro k; ext x; apply Iff.intro
  · case mp => intro h; rw [Set.mem_singleton_iff]
               dsimp [EspaceMetrique.d, induite_dist] at h
               apply Z_eq_of_sub_lt_one; linarith
  · case mpr => intro h; rw [Set.mem_singleton_iff] at h
                rw [h]; apply centre_in_boule; linarith

lemma ouverte_of_Z_induite (A : Partie Z_induite) : ouverte A := by
  intro x x_in; use (1 / 2), by linarith
  rwa [boule_in_Z_induite, Set.singleton_subset_iff]

lemma fermee_of_Z_induite (A : Partie Z_induite) : fermee A := by
  apply ouverte_of_Z_induite

-- b)

lemma Ioo_ouverte (a b : ℝ) : ouverte [a <__< b] := by
  intro x x_in; rcases x_in with ⟨h₁, h₂⟩
  use min ((x - a) / 2) ((b - x) / 2)
  apply And.intro
  · apply lt_min; repeat linarith
  · intro y y_in; unfold instEspaceMetriqueReal at y_in
    dsimp at y_in; rw [lt_min_iff] at y_in; apply And.intro
    · rw [abs_sub_lt_iff] at y_in; linarith
    · nth_rw 2 [abs_sub_lt_iff] at y_in; linarith

lemma Ioi_ouverte (a : ℝ) : ouverte [a <__< +∞] := by
  intro x x_in; dsimp at x_in
  use (x - a) / 2, by linarith
  intro y y_in; unfold instEspaceMetriqueReal at y_in
  dsimp at y_in; rw [abs_sub_lt_iff] at y_in; dsimp; linarith

lemma Iio_ouverte (b : ℝ) : ouverte [-∞ <__< b] := by
  intro x x_in; dsimp at x_in
  use (b - x) / 2, by linarith
  intro y y_in; unfold instEspaceMetriqueReal at y_in
  dsimp at y_in; rw [abs_sub_lt_iff] at y_in; dsimp; linarith

lemma Icc_fermee (a b : ℝ) : fermee [a ≤__≤ b] := by
  have int_compl : Ω \ [a ≤__≤ b] = {x | x < a ∨ x > b} := by
    ext x; simp [-not_and, not_and_or]
  rw [fermee_def, int_compl]; intro x x_in
  apply Or.by_cases x_in
  · case h₁ => intro h; have ouv := Iio_ouverte a
               rcases ouv x h with ⟨r, r_pos, hr⟩
               use r, r_pos; intro y y_in; apply Or.inl (hr y_in)
  · case h₂ => intro h; have ouv := Ioi_ouverte b
               rcases ouv x h with ⟨r, r_pos, hr⟩
               use r, r_pos; intro y y_in; apply Or.inr (hr y_in)

lemma Ici_fermee (a : ℝ) : fermee [a ≤__< +∞] := by
  have int_compl : Ω \ [a ≤__< +∞] = {x | x < a} := by
    ext x; simp
  rw [fermee_def, int_compl]; exact Iio_ouverte a

lemma Iic_fermee (b : ℝ) : fermee [-∞ <__≤ b] := by
  have int_compl : Ω \ [-∞ <__≤ b] = {x | x > b} := by
    ext x; simp
  rw [fermee_def, int_compl]; exact Ioi_ouverte b

lemma Icc_pas_ouverte {a b : ℝ} (h : a ≤ b) : ¬ ouverte [a ≤__≤ b] := by
  rw [ouverte_def]; push_neg; use a
  apply And.intro ⟨le_refl a, h⟩
  intro r r_pos; rw [Set.not_subset]; use a - r/2
  apply And.intro _ (by simp [r_pos])
  unfold instEspaceMetriqueReal; dsimp; rw [abs_lt]
  apply And.intro (by linarith) (by linarith)

lemma Ici_pas_ouverte (a : ℝ) : ¬ ouverte [a ≤__< +∞] := by
  rw [ouverte_def]; push_neg; use a
  apply And.intro (le_refl a)
  intro r r_pos; rw [Set.not_subset]; use a - r/2
  apply And.intro _ (by simp [r_pos])
  unfold instEspaceMetriqueReal; dsimp; rw [abs_lt]
  apply And.intro (by linarith) (by linarith)

lemma Iic_pas_ouverte (b : ℝ) : ¬ ouverte [-∞ <__≤ b] := by
  rw [ouverte_def]; push_neg; use b
  apply And.intro (le_refl b)
  intro r r_pos; rw [Set.not_subset]; use b + r/2
  apply And.intro _ (by simp [r_pos])
  unfold instEspaceMetriqueReal; dsimp; rw [abs_lt]
  apply And.intro (by linarith) (by linarith)

lemma Ioo_pas_fermee {a b : ℝ} (h : a < b) : ¬ fermee [a <__< b] := by
  have int_compl : Ω \ [a <__< b] = {x | x ≤ a ∨ x ≥ b} := by
    ext; simp [-not_and, not_and_or]
  rw [fermee_def, int_compl, ouverte_def]; push_neg
  use a, (by simp); intro r r_pos; rw [Set.not_subset]
  let m := min (b - a) r
  have m_pos : 0 < m := by
    rw [lt_min_iff]; apply And.intro _ r_pos; linarith
--
  have ineq₁ : m ≤ b - a := min_le_left (b - a) r
  have ineq₂ : m ≤ r := min_le_right (b - a) r
  use a + m/2; apply And.intro
  · unfold instEspaceMetriqueReal; dsimp; rw [abs_lt]
    apply And.intro (by linarith) (by linarith)
  · dsimp; push_neg; apply And.intro (by linarith) (by linarith)

lemma Ioi_pas_fermee (a : ℝ) : ¬ fermee [a <__< +∞] := by
  have int_compl : Ω \ [a <__< +∞] = {x | x ≤ a} := by
    ext x; simp
  rw [fermee_def, int_compl]; exact Iic_pas_ouverte a

lemma Iio_pas_fermee (b : ℝ) : ¬ fermee [-∞ <__< b] := by
  have int_compl : Ω \ [-∞ <__< b] = {x | x ≥ b} := by
    ext x; simp
  rw [fermee_def, int_compl]; exact Ici_pas_ouverte b

lemma Ioc_pas_ouverte {a b : ℝ} (h : a < b) : ¬ ouverte [a <__≤ b] := by
  rw [ouverte_def]; push_neg; use b
  apply And.intro ⟨h, le_refl b⟩
  intro r r_pos; rw [Set.not_subset]; use b + r/2
  apply And.intro _ (by simp [r_pos])
  unfold instEspaceMetriqueReal; dsimp; rw [abs_lt]
  apply And.intro (by linarith) (by linarith)

lemma Ioc_pas_fermee {a b : ℝ} (h : a < b) : ¬ fermee [a <__≤ b] := by
  have int_compl : Ω \ [a <__≤ b] = {x | x ≤ a ∨ x > b} := by
    ext; simp [-not_and, not_and_or]
  rw [fermee_def, int_compl, ouverte_def]; push_neg
  use a, (by simp); intro r r_pos; rw [Set.not_subset]
  let m := min (b - a) r
  have m_pos : 0 < m := by
    rw [lt_min_iff]; apply And.intro _ r_pos; linarith
--
  have ineq₁ : m ≤ b - a := min_le_left (b - a) r
  have ineq₂ : m ≤ r := min_le_right (b - a) r
  use a + m/2; apply And.intro
  · unfold instEspaceMetriqueReal; dsimp; rw [abs_lt]
    apply And.intro (by linarith) (by linarith)
  · dsimp; push_neg; apply And.intro (by linarith) (by linarith)

lemma Ico_pas_ouverte {a b : ℝ} (h : a < b) : ¬ ouverte [a ≤__< b] := by
  rw [ouverte_def]; push_neg; use a
  apply And.intro ⟨le_refl a, h⟩
  intro r r_pos; rw [Set.not_subset]; use a - r/2
  apply And.intro _ (by simp [r_pos])
  unfold instEspaceMetriqueReal; dsimp; rw [abs_lt]
  apply And.intro (by linarith) (by linarith)

lemma Ico_pas_fermee {a b : ℝ} (h : a < b) : ¬ fermee [a ≤__< b] := by
  have int_compl : Ω \ [a ≤__< b] = {x | x < a ∨ x ≥ b} := by
    ext; simp [-not_and, not_and_or]
  rw [fermee_def, int_compl, ouverte_def]; push_neg
  use b, (by simp); intro r r_pos; rw [Set.not_subset]
  let m := min (b - a) r
  have m_pos : 0 < m := by
    rw [lt_min_iff]; apply And.intro _ r_pos; linarith
--
  have ineq₁ : m ≤ b - a := min_le_left (b - a) r
  have ineq₂ : m ≤ r := min_le_right (b - a) r
  use b - m/2; apply And.intro
  · unfold instEspaceMetriqueReal; dsimp; rw [abs_lt]
    apply And.intro (by linarith) (by linarith)
  · dsimp; push_neg; apply And.intro (by linarith) (by linarith)

example : let S := [0 ≤__< 1]; ¬ ouverte S ∧ ¬ fermee S := by
  apply And.intro
  · apply Ico_pas_ouverte; linarith
  · apply Ico_pas_fermee; linarith

-- c)

section Relatifs

lemma ouverte_of_self_ind (A : Partie X) : ouverte (A : Partie Induite A)
  := by rw [self_induite]; exact ouverte_of_uni

def S : Partie ℝ := [0 ≤__< 1]
abbrev Sᵢ : Partie ℝ := Induite S

example : ouverte (S : Partie Sᵢ) := ouverte_of_self_ind S
example : ¬ ouverte (S : Partie ℝ) := Ico_pas_ouverte one_pos

lemma in_Z_induite : ∀ n : ℕ, ↑n ∈ Z := by
  intro n; use n; rw [Int.cast_natCast]

instance {n : ℕ} : OfNat Z_induite n where
  ofNat := ⟨n, in_Z_induite n⟩

example : Bₒ (0 : Z_induite) (1/2) = {0} := boule_in_Z_induite 0

example : Infinite (Bₒ (0 : ℝ) (1/2)) := by
  let B := Bₒ (0 : ℝ) (1/2)
  have N_to_B : ∀ n : ℕ, (1 : ℝ) / (n + 3) ∈ B := by
    intro n; unfold B instEspaceMetriqueReal; dsimp
    have h : (1 : ℝ) / (n + 3) > 0 := by
      apply div_pos (by linarith) (by linarith)
    rw [sub_zero, abs_of_pos h, div_lt_div_iff_of_pos_left]
    repeat linarith
--
  let f : ℕ → B := n ↦ ⟨(1 : ℝ) / (n + 3), N_to_B n⟩
  apply Infinite.of_injective f; intro m n h
  rw [←Subtype.val_inj] at h; dsimp [f] at h;
  rw [←inv_eq_one_div, ←inv_eq_one_div, inv_inj] at h
  rwa [add_right_cancel_iff, Nat.cast_inj] at h

end Relatifs

-- Proposition 1.9.

-- a)

open Famille in
@[simp] theorem ouverte_of_union {F : Famille X} (hu : ∀ A ∈ F, ouverte A) :
  ouverte (⋃ᵢ F) := by
  intro x hx; rcases hx with ⟨A, hA, x_in⟩
  rcases (hu A hA) x x_in with ⟨r, r_pos, hr⟩
  use r, r_pos; exact subset_union_famille hr hA

-- b)

@[simp] theorem ouverte_of_inter {A B : Partie X} (hA : ouverte A)
  (hB : ouverte B) : ouverte (A ∩ B) := by
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

@[simp] theorem ouv_of_boule_ouv (a : X) (r : ℝ) : ouverte (Bₒ a r) := by
  intro x hx; let r' := r - d(x, a)
  have r'_pos : r' > 0 := sub_pos_of_lt hx
  use r', r'_pos; intro y hy; dsimp; rw [←sub_add_cancel r d(x, a)]
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  apply lt_of_le_of_lt (ineq y x a); apply add_lt_add_left; exact hy

@[simp] theorem fermee_of_boule_f (a : X) (r : ℝ) : fermee (Bf a r) := by
  intro x hx; let r' := d(x, a) - r
  have hr : r < d(x, a) := by simp_all
  have r'_pos : r' > 0 := sub_pos_of_lt hr
  use r', r'_pos; intro y hy; dsimp; rw [←sub_add_cancel r d(x, a)]
  suffices h : r < d(y, a) by simp_all
  have r_lt : r < d(x, a) - d(x, y) := by
    rw [lt_sub_comm]; rwa [M.is_dist.symm]
  rw [M.is_dist.symm]; exact lt_of_lt_of_le r_lt (sub_ineq x a y)

-- d)

open Famille in
theorem ouv_eq_boule_union {U : Partie X} (h : ouverte U) : ∃ F : Famille X,
  (∀ B ∈ F, is_boule B) ∧ U = ⋃ᵢ F := by
  choose! r hr using h
  let F : Famille X := ⟨U, x ↦ Bₒ x.val (r x)⟩
  have F_is_boule : ∀ B ∈ F, is_boule B := by
    intro B hB; rcases hB with ⟨x, hx⟩; rw [←hx]; use x, r x
--
  use F, F_is_boule; ext x; apply Iff.intro
  · case mp => intro in_u; let xᵤ : U := ⟨x, in_u⟩
               rw [mem_union_famille]; use Bₒ x (r xᵤ), by use xᵤ
               apply centre_in_boule; exact (hr xᵤ in_u).left
  · case mpr => intro in_U; rcases in_U with ⟨U', hU', x_in⟩
                rcases hU' with ⟨U'', hU''⟩; dsimp at hU''
                apply (hr U'' U''.prop).right; rwa [←hU''] at x_in

-- Définition 1.10.

open Classical in
noncomputable def diam (A : Partie X) := let S := {d(x, y) | (x ∈ A) (y ∈ A)};
  if BddAbove S then sSup S else -1

@[simp] lemma diam_empty : diam (X := X) ∅ = 0 := by simp [diam]

lemma diam_nneg (A : Partie X) : diam A ≥ 0 ∨ diam A = -1 := by
  let S := {d(x, y) | (x ∈ A) (y ∈ A)}
  by_cases nonempty : Set.Nonempty A
  · case pos => dsimp [diam]; by_cases bdd : BddAbove S
                · case pos =>
                    rcases nonempty with ⟨x, hx⟩; let d := d(x, x)
                    have d_in : d ∈ S := by use x, hx, x, hx
                    apply Or.inl; rw [if_pos bdd]
                    apply le_trans (M.is_dist.nneg x x)
                    exact le_csSup bdd d_in
                · case neg => apply Or.inr; rw [if_neg bdd]
  · case neg => apply Or.inl; simp_all [Set.not_nonempty_iff_eq_empty]

def diam_bornee (A : Partie X) := diam A > -1

def dist_bornee_nneg (A : Partie X) := ∃ M ≥ 0, ∀ x y ∈ A, d(x, y) ≤ M

def dist_bornee (A : Partie X) := ∃ M, ∀ x y ∈ A, d(x, y) ≤ M
-- en général, on utilisera cette définition pour une partie bornée

def in_boule (A : Partie X) := ∃ x, ∃ r > 0, A ⊆ Bₒ x r

lemma bdd_iff_bdd_by_nneg (A : Partie X) : dist_bornee A ↔ dist_bornee_nneg A
  := by
  unfold dist_bornee dist_bornee_nneg; apply Iff.intro
  · case mp => intro h; rcases h with ⟨M, hM⟩
               use max M 0, le_max_right M 0; intro x hx y hy
               apply le_trans (hM x hx y hy); apply le_max_left
  · case mpr => intro h; rcases h with ⟨M, M_nneg, hM⟩; use M, hM

lemma bornee_iff_bdd (A : Partie X) : diam_bornee A ↔ dist_bornee A := by
  let S := {d(x, y) | (x ∈ A) (y ∈ A)}
  unfold diam_bornee dist_bornee diam; apply Iff.intro
  case mp => intro h; dsimp at h; have bdd : BddAbove S := by
              split at h
              · case isTrue _ => assumption
              · case isFalse _ => linarith
             rcases bdd with ⟨M, hM⟩; use M; intro x hx y hy
             have d_in : d(x, y) ∈ S := by use x, hx, y, hy
             exact hM d_in
--
  case mpr => intro h; rcases h with ⟨M, hM⟩; have bdd : BddAbove S := by
                use M; intro d d_in; rcases d_in with ⟨x, hx, y, hy, eq⟩
                rw [←eq]; exact hM x hx y hy
              rw [if_pos bdd]; by_cases empty : A = ∅
              · case pos => rw [empty]; simp
              · case neg =>
                rw [←ne_eq, ←Set.nonempty_iff_ne_empty] at empty
                rw [Set.nonempty_def] at empty
--
                rcases empty with ⟨x, hx⟩; refold_let S
                have nonempty : S.Nonempty := by
                  use d(x, x), x, hx, x, hx
                rw [gt_iff_lt, lt_csSup_iff bdd nonempty]
                use d(x, x); apply And.intro (by use x, hx, x, hx)
                rw [self_dist]; linarith

lemma bdd_iff_in_boule (A : Partie X) : Nonempty X ∧ dist_bornee A ↔
  in_boule A := by
  unfold in_boule; apply Iff.intro
  · case mp => rw [bdd_iff_bdd_by_nneg]; intro ⟨h₁, h₂⟩
               rcases h₂ with ⟨M, M_nneg, hM⟩; by_cases empty : A = ∅
               · case pos =>
                  rw [empty]; suffices hyp : ∃ r : ℝ, 0 < r by simp_all
                  use 1, by linarith
               · case neg =>
                  rw [←ne_eq, ←Set.nonempty_iff_ne_empty] at empty
                  rw [Set.nonempty_def] at empty
                  rcases empty with ⟨x, hx⟩; use x, M + 1, by linarith
                  intro y hy; apply lt_of_le_of_lt (hM y hy x hx); linarith
--
  · case mpr => intro h; rcases h with ⟨a, r, r_pos, in_B⟩
                rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
                apply And.intro (by use a); use r + r
                intro x hx y hy
                apply le_trans (ineq x a y); apply le_of_lt
                rw [symm a y]; exact add_lt_add (in_B hx) (in_B hy)

def bornee (X : Type) [EspaceMetrique X] := dist_bornee_nneg (X := X) Ω

-- Définition 1.11.

def converges_to (u : ℕ → X) (l : X) := ∀ ε > 0, ∃ N, ∀ n ≥ N, d(u n, l) ≤ ε

def converges (u : ℕ → X) := ∃ l, converges_to u l

def seq_bornee (u : ℕ → X) := dist_bornee {u n | n}

lemma converges_iff_c_converges (u : ℕ → X) (l : X) {C : ℝ} (C_pos : C > 0) :
  converges_to u l ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, d(u n, l) ≤ C * ε := by
  apply Iff.intro
  · case mp => intro h ε ε_pos
               rcases h (C * ε) (mul_pos C_pos ε_pos) with ⟨N, hN⟩
               use N
  · case mpr => intro h ε ε_pos
                rcases h (ε / C) (div_pos ε_pos C_pos) with ⟨N, hN⟩
                use N; intro n n_ge; have ineq := hN n n_ge
                rwa [←mul_div_assoc, mul_div_cancel_left₀] at ineq
                exact ne_of_gt C_pos

-- Remarque 1.12.

def converges_in_vois (u : ℕ → X) (l : X) := ∀ U, ouverte U → l ∈ U →
  ∃ N, ∀ n ≥ N, u n ∈ U

theorem lim_iff_lim_vois (u : ℕ → X) (l : X) : converges_to u l ↔
  converges_in_vois u l := by
  apply Iff.intro
  case mp => intro h U ouv l_in; have l_vois := ouv l l_in
             rcases l_vois with ⟨r, r_pos, hr⟩
             rcases (h (r/2) (by linarith)) with ⟨N, hN⟩
             use N; intro n hn; apply hr
             apply lt_of_le_of_lt (hN n hn); linarith
--
  case mpr => intro h' ε ε_pos; let U := Bₒ l ε
              have ouv_U := ouv_of_boule_ouv l ε
              have l_in := centre_in_boule l ε_pos
              rcases (h' U ouv_U l_in) with ⟨N, hN⟩
              use N; intro n hn; apply le_of_lt
              have u_n_in := hN n hn
              unfold U at u_n_in; apply u_n_in

-- Exemple 1.13.

-- a)

lemma inv_of_le_forall : let u : ℕ → ℝ := n ↦ 1 / (n + 1); ∀ ε > 0, ∃ N,
  ∀ n ≥ N, u n ≤ ε := by
  intro u ε ε_pos
  have arch := Real.instArchimedean.arch 1 ε_pos
  rcases arch with ⟨N, hN⟩; use N; intro n hn
  unfold u; field_simp; apply le_trans hN; rw [nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  rw [←Nat.cast_add_one, Nat.cast_le]; linarith

lemma conv_of_le_inv (v : ℕ → ℝ) (hv : ∀ n, v n ≥ 0) (h : ∀ n, v n ≤ 1 / (n + 1))
  : converges_to v 0 := by
  intro ε ε_pos
  have exists_N := inv_of_le_forall ε ε_pos
  rcases exists_N with ⟨N, hN⟩; use N; intro n hn
  dsimp [instEspaceMetriqueReal]
  rw [sub_zero, abs_of_nonneg (hv n)]
  exact le_trans (h n) (hN n hn)

theorem conv_of_inv : let u : ℕ → ℝ := n ↦ 1 / (n + 1); converges_to u 0 := by
  intro u; apply conv_of_le_inv u
  · intro n; unfold u; field_simp; linarith
  · intro n; linarith

-- b)

theorem bornee_of_conv (u : ℕ → X) (h : converges u) : seq_bornee u := by
  rcases h with ⟨l, hl⟩; rcases hl 1 one_pos with ⟨N, hN⟩
  have bdd : BddAbove {d(u n, l) | n : Fin N} := by
    apply SupReal.bddabove_of_fin_image
  rcases bdd with ⟨M, hM⟩; unfold seq_bornee
  apply And.right; rw [bdd_iff_in_boule]
  let M' := max (M + 1) 2
  use l, M', lt_max_of_lt_right (zero_lt_two)
  intro x hx; rcases hx with ⟨n, hn⟩; rw [←hn]; dsimp
--
  by_cases lt : n < N
  · case pos =>
      have u_n_in : d(u n, l) ∈ {d(u n, l) | n : Fin N}
        := by use ⟨n, lt⟩
      apply lt_max_of_lt_left
      exact lt_of_le_of_lt (hM u_n_in) (by linarith)
  · case neg =>
      push_neg at lt; apply lt_max_of_lt_right
      exact lt_of_le_of_lt (hN n lt) (by linarith)

-- 1.3. Espaces métriques complets (I)

-- Définition 1.14.

def cauchy (u : ℕ → X) := ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, d(u m, u n) ≤ ε

-- Proposition 1.15.

-- a)

theorem cauchy_of_conv (u : ℕ → X) (h : converges u) : cauchy u := by
  rcases h with ⟨l, hl⟩; intro ε ε_pos
  rcases (hl (ε / 2) (by linarith)) with ⟨N, hN⟩
  use N; intro m hm n hn
  rcases M.is_dist with ⟨nneg, sep, symm, ineq⟩
  have ineq₁ := ineq (u m) l (u n)
  have ineq₂ := hN m hm; have ineq₃ := hN n hn
  rw [symm l (u n)] at ineq₁; linarith

-- b)

theorem bornee_of_cauchy (u : ℕ → X) (h : cauchy u) : seq_bornee u := by
  sorry

-- c)

def extraction (φ : ℕ → ℕ) := ∀ m n, m < n → φ m < φ n

lemma extract_equiv (φ : ℕ → ℕ) : extraction φ ↔ ∀ n, φ n < φ (n+1) := by
  constructor
  · intro hφ; unfold extraction at hφ; intro n
    specialize hφ n (n+1) (by linarith); exact hφ
  · intro h; unfold extraction
    intro m n hlt; rw [Nat.lt_iff_add_one_le] at hlt
    induction n
    · case zero => linarith
    · case succ n hn =>
        by_cases h1 : m+1 = n+1
        · rw [←h1]; specialize h m; exact h
        · have m_lt_n : m < n := by
            push_neg at h1; rw [lt_iff_le_and_ne]
            apply And.intro (by linarith)
            rwa [←Nat.add_one_ne_add_one_iff]
          rw [Nat.lt_iff_add_one_le] at m_lt_n
          have hφmn : φ m < φ n := hn m_lt_n
          apply lt_trans hφmn (h n)

lemma n_le_extr_n {φ : ℕ → ℕ} (h : extraction φ) : ∀ n, n ≤ φ n := by
  intro n; induction n
  · case zero => apply zero_le
  · case succ k hk => apply Nat.le_of_pred_lt; rw [Nat.pred_succ]
                      apply lt_of_le_of_lt hk; apply h; linarith

lemma extr_conv_infini {φ : ℕ → ℕ} (h : extraction φ) : ∀ A : ℕ, ∃ N : ℕ, ∀ n ≥ N,
  φ n ≥ A := by
  intro A; use A
  intro n hn
  trans n
  · exact n_le_extr_n h n
  · exact hn

theorem conv_of_cauchy_extr (u : ℕ → X) (h : cauchy u) (φ : ℕ → ℕ)
  (hφ : extraction φ) (conv : converges (u ∘ φ)) : converges u := by
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

def complet (X : Type) [EspaceMetrique X] := ∀ u : ℕ → X, cauchy u →
  converges u
