-- import TopoTER.SetElem
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
-- import Mathlib.Algebra.DirectSum.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

-- Préliminaires

namespace TER

scoped syntax (name := quickfun) term " ↦ " term : term
macro_rules (kind := quickfun)
  | `($x ↦ $desc) => `(fun $x => $desc)

scoped syntax (name := auxpred) "[" ident "," ident,+ "]" term "," term : term
macro_rules (kind := auxpred)
  | `([$x, $y] $S, $desc) => `(∀ ($x), $x ∈ $S → ∀ ($y), $y ∈ $S → $desc)
  | `([$x, $y, $z,*] $S, $desc) => `(∀ ($x), $x ∈ $S → [$y, $z,*] $S, $desc)

scoped syntax (name := for_all) "∀ " ident ident+ " ∈ " term ", " term : term
macro_rules (kind := for_all)
  | `(∀ $x $y* ∈ $S, $desc) => `([$x, $y,*] $S, $desc)

abbrev R : Set ℝ := Set.univ

abbrev R_star : Set ℝ := {x : ℝ | x ≠ 0}
notation "Rˣ" => R_star

abbrev R_pos : Set ℝ := {x : ℝ | x ≥ 0}
notation "R₊" => R_pos

abbrev R_neg : Set ℝ := {x : ℝ | x ≤ 0}
notation "R₋" => R_neg

abbrev R_star_pos : Set ℝ := {x : ℝ | x > 0}
notation "R₊ˣ" => R_star_pos

abbrev R_star_neg : Set ℝ := {x : ℝ | x < 0}
notation "R₋ˣ" => R_star_neg

abbrev C : Set ℂ := Set.univ

abbrev C_star : Set ℂ := {x : ℂ | x ≠ 0}
notation "Cˣ" => C_star

open Real Complex
namespace Complex

noncomputable def module (z : ℂ) : ℝ := √(normSq z)
scoped notation "‖"z"‖ᵢ" => module z

theorem norm_nonneg (z : ℂ) : ‖z‖ᵢ ≥ 0 := by apply sqrt_nonneg

theorem norm_eq_zero (z : ℂ) : ‖z‖ᵢ = 0 ↔ z = 0 := by
  unfold module; rw [sqrt_eq_zero, normSq_eq_zero]; apply normSq_nonneg

theorem norm_zero : ‖0‖ᵢ = 0 := by rw [norm_eq_zero]

theorem norm_pos {z : ℂ} (h : z ≠ 0) : ‖z‖ᵢ > 0 := by
  apply lt_of_le_of_ne (norm_nonneg z)
  intro h'; absurd h; rw [←norm_eq_zero]; symm; exact h'

theorem norm_symm (z : ℂ) : ‖z‖ᵢ = ‖-z‖ᵢ := by
  dsimp [module, normSq]; rw [neg_mul_neg, neg_mul_neg]

lemma norm_add_one (z : ℂ) : ‖z + 1‖ᵢ ≤ ‖z‖ᵢ + 1 := by
  dsimp [module, normSq]; apply le_of_sq_le_sq
  · rw [add_sq, sq_sqrt, sq_sqrt, sq, mul_one, one_mul]
    · rw [add_zero, add_mul_self_eq, mul_one, one_mul]
      have ineq : 2 * z.re ≤ 2 * √(z.re * z.re + z.im * z.im) := by
        apply mul_le_mul_of_nonneg_left (ha := zero_le_two)
        apply le_sqrt_of_sq_le; rw [sq]
        apply le_add_of_nonneg_right; apply mul_self_nonneg
--
      let re2 := z.re * z.re; let im2 := z.im * z.im; refold_let re2 im2
      calc re2 + 2 * z.re + 1 + im2
      _ = re2 + im2 + 1 + 2 * z.re := by ring
      _ ≤ re2 + im2 + 1 + 2 * √(re2 + im2) := by apply add_le_add_right ineq
      _ = re2 + im2 + 2 * √(re2 + im2) + 1 := by ring
    · apply normSq_nonneg
    · apply normSq_nonneg (z + 1)
  · apply add_nonneg (hb := zero_le_one); apply sqrt_nonneg

theorem norm_mul (z w : ℂ) : ‖z * w‖ᵢ = ‖z‖ᵢ * ‖w‖ᵢ := by
  unfold module; rw [←sqrt_mul (normSq_nonneg z), normSq_mul]

theorem norm_div (z w : ℂ) : ‖z / w‖ᵢ = ‖z‖ᵢ / ‖w‖ᵢ := by
  unfold module; rw [←sqrt_div (normSq_nonneg z), normSq_div]

theorem norm_ineq (z w : ℂ) : ‖z + w‖ᵢ ≤ ‖z‖ᵢ + ‖w‖ᵢ := by
  by_cases eq_zero : w = 0
  · rw [eq_zero, add_zero, norm_zero, add_zero]
  · have pos : ‖w‖ᵢ > 0 := norm_pos eq_zero
    apply (div_le_div_iff_of_pos_right pos).mp
    rw [←norm_div]; repeat rw [add_div, div_self]
    · rw [←norm_div]; apply norm_add_one
    · exact ne_of_gt pos
    · exact eq_zero

end Complex

namespace VectorSpace

class Euclidean (E : Type*) [AddCommGroup E] [Module ℝ E]
  extends FiniteDimensional ℝ E where
  scalar : E → E → ℝ
  symm (u v : E) : scalar u v = scalar v u
  add_left (u v w : E) : scalar (u + v) w = scalar u w + scalar v w
  smul_left (u v : E) (k : ℝ) : scalar (k • u) v = k * (scalar u v)
  pos (u : E) : scalar u u ≥ 0
  definie (u : E) : scalar u u = 0 ↔ u = 0

class ValuationField (K : Type*) [Field K] where
  abs : K → ℝ
  isAbv : IsAbsoluteValue abs

instance : ValuationField ℝ where
  abs := abs
  isAbv := IsAbsoluteValue.abs_isAbsoluteValue

open Complex in
instance module_abs : IsAbsoluteValue module where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := @norm_eq_zero
  abv_add' := norm_ineq
  abv_mul' := norm_mul

open Complex in
noncomputable instance : ValuationField ℂ where
  abs := module
  isAbv := module_abs

@[ext]
structure R_n (n : ℕ) where
  p : ℕ → ℝ
  is_fin : ∀ m ≥ n, p m = 0

notation : max "ℝ^" n : max => R_n n

namespace R_n

@[simp] instance {n : ℕ} : HAdd ℝ^n ℝ^n ℝ^n where
  hAdd := x ↦ y ↦ ⟨
    x.p + y.p, by {
      intro m m_ge; rw [Pi.add_apply]
      rw [x.is_fin m m_ge, y.is_fin m m_ge, zero_add]
    }
  ⟩

@[simp] instance {n : ℕ} : HSub ℝ^n ℝ^n ℝ^n where
  hSub := x ↦ y ↦ ⟨
    x.p - y.p, by {
      intro m m_ge; rw [Pi.sub_apply]
      rw [x.is_fin m m_ge, y.is_fin m m_ge, sub_zero]
    }
  ⟩

@[simp] instance {n : ℕ} : Zero ℝ^n where
  zero := ⟨0, by simp⟩

@[simp] instance {n : ℕ} : Neg ℝ^n where
  neg := x ↦ ⟨
    -x.p, by {
      intro m m_ge; rw [Pi.neg_apply]
      rw [x.is_fin m m_ge, neg_zero]
    }
  ⟩

@[simp] instance {n : ℕ} : SMul ℕ ℝ^n where
  smul := k ↦ x ↦ ⟨
    k * x.p, by {
      intro m m_ge; rw [Pi.mul_apply]
      rw [x.is_fin m m_ge, mul_zero]
    }
  ⟩

@[simp] instance {n : ℕ} : SMul ℤ ℝ^n where
  smul := k ↦ x ↦ ⟨
    k * x.p, by {
      intro m m_ge; rw [Pi.mul_apply]
      rw [x.is_fin m m_ge, mul_zero]
    }
  ⟩

@[simp] instance {n : ℕ} : SMul ℝ ℝ^n where
  smul := r ↦ x ↦ ⟨
    k ↦ r * x.p k, by {
      intro m m_ge; dsimp
      rw [x.is_fin m m_ge, mul_zero]
    }
  ⟩

@[simp] theorem add_assoc {n : ℕ} (x y z : ℝ^n) : x + y + z = x + (y + z)
  := by dsimp; ring_nf

@[simp] theorem add_comm {n : ℕ} (x y : ℝ^n) : x + y = y + x := by
  dsimp; ring_nf

@[simp] theorem zero_add {n : ℕ} (x : ℝ^n) : 0 + x = x := by
  rw [Zero.toOfNat0]; simp

@[simp] theorem add_zero {n : ℕ} (x : ℝ^n) : x + 0 = x := by
  rw [add_comm, zero_add]

@[simp] theorem neg_add_cancel {n : ℕ} (x : ℝ^n) : -x + x = 0 := by
  dsimp; ring_nf; rfl

@[simp] theorem add_neg_cancel {n : ℕ} (x : ℝ^n) : x + (-x) = 0 := by
  rw [add_comm, neg_add_cancel]

@[simp] theorem zero_nsmul {n : ℕ} (x : ℝ^n) : 0 • x = 0 := by
  simp [HSMul.hSMul]; rfl

@[simp] theorem zero_zsmul {n : ℕ} (x : ℝ^n) : (0 : ℤ) • x = 0 := by
  simp [HSMul.hSMul]; rfl

@[simp] theorem zero_rsmul {n : ℕ} (x : ℝ^n) : (0 : ℝ) • x = 0 := by
  simp [HSMul.hSMul]; rfl

@[simp] theorem rsmul_zero {n : ℕ} (r : ℝ) : r • (0 : ℝ^n) = 0 := by
  rw [Zero.toOfNat0]; simp [HSMul.hSMul]; rfl

@[simp] theorem one_nsmul {n : ℕ} (x : ℝ^n) : 1 • x = x := by
  simp [HSMul.hSMul]

@[simp] theorem one_zsmul {n : ℕ} (x : ℝ^n) : (1 : ℤ) • x = x := by
  simp [HSMul.hSMul]

@[simp] theorem one_rsmul {n : ℕ} (x : ℝ^n) : (1 : ℝ) • x = x := by
  simp [HSMul.hSMul]

@[simp] theorem cast_zsmul {n : ℕ} (k : ℕ) (x : ℝ^n) : (k : ℤ) • x =
  k • x := by
  simp [HSMul.hSMul]

@[simp] theorem neg_smul {n : ℕ} (k : ℤ) (x : ℝ^n) : -k • x = -(k • x)
  := by simp [HSMul.hSMul]

@[simp] theorem add_nsmul {n : ℕ} (k m : ℕ) (x : ℝ^n) : (k + m) • x =
  k • x + m • x := by
  simp [HSMul.hSMul]; ring

@[simp] theorem add_zsmul {n : ℕ} (k m : ℤ) (x : ℝ^n) : (k + m) • x =
  k • x + m • x := by
  simp [HSMul.hSMul]; ring

@[simp] theorem add_rsmul {n : ℕ} (r s : ℝ) (x : ℝ^n) : (r + s) • x =
  r • x + s • x := by
  simp [HSMul.hSMul]; ring_nf; rfl

@[simp] theorem rsmul_add {n : ℕ} (r : ℝ) (x y : ℝ^n) : r • (x + y) =
  r • x + r • y := by
  simp [HSMul.hSMul]; ring_nf; rfl

@[simp] theorem mul_rsmul {n : ℕ} (r s : ℝ) (x : ℝ^n) : (r * s) • x =
  r • s • x := by
  simp [HSMul.hSMul]; ring_nf

instance {n : ℕ} : AddCommGroup ℝ^n where
  add := x ↦ y ↦ x + y
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero

  nsmul := k ↦ x ↦ k • x
  zsmul := k ↦ x ↦ k • x
  neg_add_cancel := neg_add_cancel
  add_comm := add_comm

  nsmul_zero := zero_nsmul
  nsmul_succ := by simp
  zsmul_zero' := zero_nsmul
  zsmul_succ' := by simp
  zsmul_neg' := by
    simp [Int.negSucc_eq, -add_comm]


instance {n : ℕ} : Module ℝ ℝ^n where
  smul := r ↦ x ↦ r • x
  mul_smul := mul_rsmul
  one_smul := one_rsmul
  smul_zero := rsmul_zero
  smul_add := rsmul_add
  add_smul := add_rsmul
  zero_smul := zero_rsmul

end R_n

def S' (α : Type*) : Set α := Set.univ
scoped postfix : max "↑" => S'

scoped syntax (name := dot_prod) "⟨" term ", " term "⟩" : term
macro_rules (kind := dot_prod)
  | `(⟨$x, $y⟩) => `(Euclidean.scalar $x $y)

scoped notation : max "|"x"|" => ValuationField.abs x
variable {K : Type*} [Field K] [VF : ValuationField K]

theorem abs_zero : |(0 : K)| = 0 := by
  rcases VF.isAbv with ⟨nneg, defi, add, mul⟩; rw [defi]

theorem abs_one : |(1 : K)| = 1 := by
  rcases VF.isAbv with ⟨nneg, defi, add, mul⟩
  have eq : |(1 : K)| * |(1 : K)| = |(1 : K)| := by
    rw [←mul, one_mul]
  rw [mul_left_eq_self₀] at eq; rcases eq with pos | neg
  · case inl => assumption
  · case inr => absurd neg; rw [defi]; apply one_ne_zero

theorem abs_neg_one : |(-1 : K)| = 1 := by
  rcases VF.isAbv with ⟨nneg, defi, add, mul⟩
  have eq : |(-1 : K)| * |(-1 : K)| = 1 := by
    rw [←mul, neg_one_mul, neg_neg, abs_one]
  rw [mul_self_eq_one_iff] at eq; rcases eq with pos | neg
  · case inl => assumption
  · case inr => linarith [nneg (-1)]

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [EuclidE : Euclidean E]

theorem prod_symm (u v : E) : ⟨u, v⟩ = ⟨v, u⟩ := EuclidE.symm u v

theorem prod_add_left (u v w : E) : ⟨u + v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩ :=
  EuclidE.add_left u v w

theorem prod_smul_left (u v : E) (k : ℝ) : ⟨k • u, v⟩ = k * ⟨u, v⟩ :=
  EuclidE.smul_left u v k

theorem prod_add_right (u v w : E) : ⟨u, v + w⟩ = ⟨u, v⟩ + ⟨u, w⟩ := by
  rw [prod_symm, prod_add_left, prod_symm, prod_symm u w]

theorem prod_smul_right (u v : E) (k : ℝ) : ⟨u, k • v⟩ = k * ⟨u, v⟩ := by
  rw [prod_symm, prod_smul_left, prod_symm]

theorem prod_pos (u : E) : ⟨u, u⟩ ≥ 0 := EuclidE.pos u

theorem prod_definie (u : E) : ⟨u, u⟩ = 0 ↔ u = 0 := EuclidE.definie u

theorem prod_definie' (u : E) : ⟨u, u⟩ ≠ 0 ↔ u ≠ 0 := by
  apply Iff.ne; apply prod_definie

theorem neg_prod (u v : E) : ⟨-u, v⟩ = -⟨u, v⟩ := by
  rw [←neg_one_mul, ←prod_smul_left, neg_one_smul]

theorem prod_neg (u v : E) : ⟨u, -v⟩ = -⟨u, v⟩ := by
  rw [←neg_one_mul, ←prod_smul_right, neg_one_smul]

theorem add_prod_add (u v : E) : ⟨u + v, u + v⟩ = ⟨u, u⟩ + ⟨v, v⟩ + 2 * ⟨u, v⟩
  := by
  rw [prod_add_left, prod_add_right, prod_add_right, prod_symm u v]; ring

theorem sub_prod_sub (u v : E) : ⟨u - v, u - v⟩ = ⟨u, u⟩ + ⟨v, v⟩ - 2 * ⟨u, v⟩
  := by
  rw [sub_eq_add_neg, add_prod_add, neg_prod, prod_neg, neg_neg]
  rw [prod_neg, mul_neg, sub_eq_add_neg]

theorem zero_prod (u : E) : ⟨0, u⟩ = 0 := by
  have eq : ⟨0, u⟩ = ⟨0, u⟩ := by rfl
  nth_rewrite 2 [←neg_zero] at eq; rw [neg_prod] at eq
  apply CharZero.eq_neg_self_iff.mp eq

theorem prod_zero (u : E) : ⟨u, 0⟩ = 0 := by
  rw [prod_symm, zero_prod]

theorem am_gm_ineq (u v : E) : ⟨u, u⟩ + ⟨v, v⟩ ≥ 2 * ⟨u, v⟩ := by
  apply le_of_sub_nonneg; rw [←sub_prod_sub]; apply prod_pos

noncomputable def norm (u : E) : ℝ := √⟨u, u⟩
scoped notation "‖"u"‖ₑ" => norm u

theorem norm_nonneg (u : E) : ‖u‖ₑ ≥ 0 := by apply sqrt_nonneg

theorem norm_eq_zero (u : E) : ‖u‖ₑ = 0 ↔ u = 0 := by
  unfold norm; rw [sqrt_eq_zero, prod_definie]; apply prod_pos

theorem norm_zero : ‖(0 : E)‖ₑ = 0 := by rw [norm_eq_zero]

theorem norm_pos {u : E} (h : u ≠ 0) : ‖u‖ₑ > 0 := by
  apply lt_of_le_of_ne (norm_nonneg u)
  intro h'; absurd h; rw [←norm_eq_zero]; symm; exact h'

theorem norm_symm (u : E) : ‖u‖ₑ = ‖-u‖ₑ := by
  unfold norm; rw [prod_neg, neg_prod, neg_neg]

@[simp] noncomputable local instance : HDiv E ℝ E where
  hDiv := u ↦ x ↦ x⁻¹ • u

-- pour éviter la confusion avec la division scalaire:
local infix : 78 " ∣ " => @HDiv.hDiv ℝ ℝ ℝ instHDiv

lemma div_prod_div (u v : E) (x y : ℝ) : ⟨u / x, v / y⟩ = ⟨u, v⟩ ∣ (x * y)
  := by
  dsimp; rw [prod_smul_left, prod_smul_right]
  rw [←mul_assoc, ←mul_inv, ←div_eq_inv_mul]

theorem div_norm_sq {u : E} (h : u ≠ 0) : ⟨u / ‖u‖ₑ, u / ‖u‖ₑ⟩ = 1 := by
  unfold norm; rw [div_prod_div, mul_self_sqrt (prod_pos u)]
  rw [div_self]; rw [prod_definie']; exact h

theorem cauchy_schwarz (u v : E) : ⟨u, v⟩ ≤ ‖u‖ₑ * ‖v‖ₑ := by
  by_cases h : u = 0
  case pos => rw [h, zero_prod, norm_zero, zero_mul]
  case neg =>
    by_cases h' : v = 0
    case pos => rw [h', prod_zero, norm_zero, mul_zero]
    case neg =>
      have pos : ‖u‖ₑ * ‖v‖ₑ > 0 := by
        exact mul_pos (norm_pos h) (norm_pos h')
      have ineq := am_gm_ineq (u / ‖u‖ₑ) (v / ‖v‖ₑ)
      rw [div_norm_sq h, div_norm_sq h', div_prod_div] at ineq
      rw [←div_le_one pos]; linarith

theorem norm_ineq (u v : E) : ‖u + v‖ₑ ≤ ‖u‖ₑ + ‖v‖ₑ := by
  unfold norm; apply le_of_sq_le_sq
  · rw [add_prod_add, add_sq, sq_sqrt, sq_sqrt, sq_sqrt]
    · rw [←norm, ←norm]; linarith [cauchy_schwarz u v]
    repeat apply prod_pos
    · rw [←add_prod_add]; apply prod_pos
  · rw [←norm, ←norm]; apply add_nonneg; repeat apply norm_nonneg

end VectorSpace
end TER
