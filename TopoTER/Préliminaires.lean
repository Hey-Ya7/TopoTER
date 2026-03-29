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

abbrev Ω {α} : Set α := Set.univ
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

instance : Coe ℝ R := ⟨r ↦ ⟨r, by simp⟩⟩
instance : Coe ℂ C := ⟨z ↦ ⟨z, by simp⟩⟩

open Real Complex
namespace SupReal

@[simp] instance : HSMul ℝ (Set ℝ) (Set ℝ) where
  hSMul := r ↦ S ↦ {r * s | s ∈ S}

theorem image_of_fin {α} {n : ℕ} (f : Fin n → α) : Finite {f i | i} := by
  apply Set.Finite.of_surjOn f (s := Set.univ)
  · intro x hx; rcases hx with ⟨i, hi⟩; use i, by simp
  · apply Set.finite_univ

theorem bddabove_of_fin_image {n} (f : Fin n → ℝ) : BddAbove {f i | i} := by
  apply Set.Finite.bddAbove; apply image_of_fin

lemma bddabove_of_const {s} {c : ℝ} (h : ∀ x ∈ s, x = c) : BddAbove s := by
  use c; intro x x_in; exact le_of_eq (h x x_in)

theorem sSup_const {s : Set ℝ} {c : ℝ} (h : s.Nonempty) (h₂ : ∀ x ∈ s, x = c)
  : sSup s = c := by
  apply le_antisymm
  · apply csSup_le h; intro x x_in; exact le_of_eq (h₂ x x_in)
  · apply le_csSup (bddabove_of_const h₂); rcases h with ⟨x, x_in⟩
    rw [←h₂ x x_in]; exact x_in

instance {α} [HAdd α α α] : HAdd (Set α) (Set α) (Set α) where
  hAdd := S ↦ T ↦ {u.fst + u.snd | u ∈ Set.prod S T}

theorem add_nonempty {α} [HAdd α α α] {S T : Set α} (hs : S.Nonempty)
  (ht : T.Nonempty) : (S + T).Nonempty := by
  rcases hs with ⟨s, s_in⟩; rcases ht with ⟨t, t_in⟩
  use s + t; use ⟨s, t⟩, ⟨s_in, t_in⟩

theorem add_bddabove {S T : Set ℝ} (hs : BddAbove S) (ht : BddAbove T) :
  BddAbove (S + T) := by
  rcases hs with ⟨s, s_sup⟩; rcases ht with ⟨t, t_sup⟩
  use s + t; intro v v_in; rcases v_in with ⟨u, u_in, hu⟩
  rcases u_in with ⟨in_s, in_t⟩
  rw [←hu]; apply add_le_add
  · apply s_sup in_s
  · apply t_sup in_t

theorem sSup_add_ineq {S T : Set ℝ} (hs : S.Nonempty) (hs' : BddAbove S)
  (ht : T.Nonempty) (ht' : BddAbove T) : sSup (S + T) ≤ sSup S + sSup T := by
  have h := add_nonempty hs ht
  apply csSup_le h; intro v v_in
  rcases v_in with ⟨u, u_in, hu⟩
  rcases u_in with ⟨in_s, in_t⟩
  rw [←hu]; apply add_le_add
  · apply le_csSup hs' in_s
  · apply le_csSup ht' in_t

theorem sSup_le_sSup {S T : Set ℝ} (hs : S.Nonempty) (ht : BddAbove T)
  (h : ∀ s ∈ S, ∃ t ∈ T, s ≤ t) : sSup S ≤ sSup T := by
  apply csSup_le hs; intro s s_in
  rcases h s s_in with ⟨t, t_in, le_t⟩
  apply le_csSup_of_le ht t_in le_t

end SupReal

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
    rw [←norm_div]; rw [add_div, div_self eq_zero]
    rw [add_div, div_self (ne_of_gt pos)]
    rw [←norm_div]; apply norm_add_one

end Complex

namespace Valuation

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

scoped syntax : max (name := abs) atomic("|" noWs) term "|ₖ" : term
macro_rules (kind := abs)
  | `(|$x|ₖ) => `(ValuationField.abs $x)

variable {K : Type*} [Field K] [VF : ValuationField K]

theorem abs_nonneg (k : K) : 0 ≤ |k|ₖ := by
  apply VF.isAbv.abv_nonneg

@[simp] theorem abs_definie (k : K) : |k|ₖ = 0 ↔ k = 0 := by
  apply VF.isAbv.abv_eq_zero

@[simp] theorem abs_mul_homo (k₁ k₂ : K) : |k₁|ₖ * |k₂|ₖ = |k₁ * k₂|ₖ := by
  rw [VF.isAbv.abv_mul]

@[simp] theorem abs_sq (k : K) : |k|ₖ ^ 2 = |k ^ 2|ₖ := by simp [sq]

theorem abs_add_ineq (k₁ k₂ : K) : |k₁ + k₂|ₖ ≤ |k₁|ₖ + |k₂|ₖ := by
  apply VF.isAbv.abv_add

@[simp] theorem abs_zero : |(0 : K)|ₖ = 0 := by simp

@[simp] theorem abs_one : |(1 : K)|ₖ = 1 := by
  rcases VF.isAbv with ⟨nneg, defi, add, mul⟩
  have eq : |(1 : K)|ₖ * |(1 : K)|ₖ = |(1 : K)|ₖ := by
    rw [←mul, one_mul]
  rw [mul_left_eq_self₀] at eq; rcases eq with pos | neg
  · case inl => assumption
  · case inr => absurd neg; rw [defi]; apply one_ne_zero

@[simp] theorem abs_neg_one : |(-1 : K)|ₖ = 1 := by
  rcases VF.isAbv with ⟨nneg, defi, add, mul⟩
  have eq : |(-1 : K)|ₖ * |(-1 : K)|ₖ = 1 := by
    rw [←mul, neg_one_mul, neg_neg, abs_one]
  rw [mul_self_eq_one_iff] at eq; rcases eq with pos | neg
  · case inl => assumption
  · case inr => linarith [nneg (-1)]

theorem abs_le_zero (k : K) (hk : |k|ₖ ≤ 0) : k = 0 := by
  rw [←abs_definie]; apply le_antisymm hk (abs_nonneg k)

end Valuation

@[simp] theorem Fin.sum_trunc_last {α : Type*} [AddCommGroup α] (n : ℕ)
  (u : ℕ → α) :  ∑ i : Fin (n + 1), u i = ∑ i : Fin n, u i + u n := by
  let u' : Fin (n + 1) → α := i ↦ u i
  refold_let u'; rw [Fin.sum_univ_castSucc]; simp

namespace VectorSpace

class Euclidean (E : Type*) [AddCommGroup E] [Module ℝ E]
  extends FiniteDimensional ℝ E where
  scalar : E → E → ℝ
  symm (u v : E) : scalar u v = scalar v u
  add_left (u v w : E) : scalar (u + v) w = scalar u w + scalar v w
  smul_left (u v : E) (k : ℝ) : scalar (k • u) v = k * (scalar u v)
  pos (u : E) : scalar u u ≥ 0
  definie (u : E) : scalar u u = 0 ↔ u = 0

@[ext]
structure K_n (K : Type*) [Field K] (n : ℕ) where
  p : Fin n → K

notation : max K : max "^" n : max => K_n K n

namespace K_n
variable {K : Type*} {n : ℕ} [Field K]

@[simp] instance : HAdd K^n K^n K^n where
  hAdd := x ↦ y ↦ ⟨x.p + y.p⟩

@[simp] instance : HSub K^n K^n K^n where
  hSub := x ↦ y ↦ ⟨x.p - y.p⟩

@[simp] instance : Zero K^n where
  zero := ⟨0⟩

@[simp] instance : Neg K^n where
  neg := x ↦ ⟨-x.p⟩

@[simp] instance : SMul ℕ K^n where
  smul := k ↦ x ↦ ⟨k * x.p⟩

@[simp] instance : SMul ℤ K^n where
  smul := k ↦ x ↦ ⟨k * x.p⟩

@[simp] instance : SMul K K^n where
  smul := r ↦ x ↦ ⟨k ↦ r * x.p k⟩

@[simp] theorem add_assoc (x y z : K^n) : x + y + z = x + (y + z) := by
  dsimp; ring_nf

@[simp] theorem add_comm (x y : K^n) : x + y = y + x := by
  dsimp; ring_nf

@[simp] theorem zero_add (x : K^n) : 0 + x = x := by
  rw [Zero.toOfNat0]; simp

@[simp] theorem add_zero (x : K^n) : x + 0 = x := by
  rw [add_comm, zero_add]

@[simp] theorem neg_add_cancel (x : K^n) : -x + x = 0 := by
  dsimp; ring_nf; rfl

@[simp] theorem add_neg_cancel (x : K^n) : x + (-x) = 0 := by
  rw [add_comm, neg_add_cancel]

@[simp] theorem zero_nsmul (x : K^n) : 0 • x = 0 := by
  simp [HSMul.hSMul]; rfl

@[simp] theorem zero_zsmul (x : K^n) : (0 : ℤ) • x = 0 := by
  simp [HSMul.hSMul]; rfl

@[simp] theorem zero_ksmul (x : K^n) : (0 : K) • x = 0 := by
  simp [HSMul.hSMul]; rfl

@[simp] theorem ksmul_zero (k : K) : k • (0 : K^n) = 0 := by
  rw [Zero.toOfNat0]; simp [HSMul.hSMul]; rfl

@[simp] theorem one_nsmul (x : K^n) : 1 • x = x := by
  simp [HSMul.hSMul]

@[simp] theorem one_zsmul (x : K^n) : (1 : ℤ) • x = x := by
  simp [HSMul.hSMul]

@[simp] theorem one_ksmul (x : K^n) : (1 : K) • x = x := by
  simp [HSMul.hSMul]

@[simp] theorem cast_zsmul (m : ℕ) (x : ℝ^n) : (m : ℤ) • x =
  m • x := by
  simp [HSMul.hSMul]

@[simp] theorem neg_smul (m : ℤ) (x : K^n) : -m • x = -(m • x) := by
  simp [HSMul.hSMul]

@[simp] theorem add_nsmul (m₁ m₂ : ℕ) (x : K^n) : (m₁ + m₂) • x =
  m₁ • x + m₂ • x := by
  simp [HSMul.hSMul]; ring

@[simp] theorem add_zsmul (k m : ℤ) (x : K^n) : (k + m) • x =
  k • x + m • x := by
  simp [HSMul.hSMul]; ring

@[simp] theorem add_ksmul (k₁ k₂ : K) (x : K^n) : (k₁ + k₂) • x =
  k₁ • x + k₂ • x := by
  simp [HSMul.hSMul]; ring_nf; rfl

@[simp] theorem ksmul_add (k : K) (x y : K^n) : k • (x + y) =
  k • x + k • y := by
  simp [HSMul.hSMul]; ring_nf; rfl

@[simp] theorem mul_ksmul (k₁ k₂ : K) (x : K^n) : (k₁ * k₂) • x =
  k₁ • k₂ • x := by
  simp [HSMul.hSMul]; ring_nf

@[simp] theorem eq_zero_iff (x : K^n) : x = 0 ↔ ∀ i, x.p i = 0 := by
  apply Iff.intro
  · case mp => intro h i; rw [h]; rfl
  · case mpr => intro h; ext i; exact h i

instance : AddCommGroup K^n where
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
  zsmul_zero' := zero_zsmul
  zsmul_succ' := by simp
  zsmul_neg' := by
    simp [Int.negSucc_eq, -add_comm]

instance : Module K K^n where
  smul := r ↦ x ↦ r • x
  mul_smul := mul_ksmul
  one_smul := one_ksmul
  smul_zero := ksmul_zero
  smul_add := ksmul_add
  add_smul := add_ksmul
  zero_smul := zero_ksmul

@[simp] theorem sum_distrib (u : Fin n → K ^ n) : (∑ i, u i).p = ∑ i, (u i).p
  := by
  let u' : ℕ → K^n := j ↦ if h : j < n then (u ⟨j, h⟩) else 0
  have recur : ∀ j, (∑ i : Fin j, u' i).p = ∑ i : Fin j, (u' i).p := by
    intro j; induction j
    case zero => simp; rfl
    case succ k hk =>
        let p' : ℕ → Fin n → K := i ↦ (u' i).p
        rw [Fin.sum_trunc_last, Fin.sum_trunc_last (u := p')]
        rw [add_comm]; simp [hk]; ring
--
  have sum_eq : ∑ i, u i = ∑ i : Fin n, u' i := by
    congr; ext i; unfold u'; rw [dif_pos]
  rw [sum_eq, recur]; congr; ext i; unfold u'; rw [dif_pos]

def canonBasis (K : Type*) [Field K] (i : Fin n) : K^n where
  p := k ↦ if i = k then 1 else 0

theorem inCanonBasis (x : K^n) : x = ∑ i, (x.p i) • canonBasis K i := by
  ext i; rw [sum_distrib, Finset.sum_apply]; unfold canonBasis
  simp only [instHSMul, instSMul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro b _ hb; apply if_neg; by_contra eq; exact hb eq
  · intro h; absurd h; apply Finset.mem_univ

end K_n

def S' (α : Type*) : Set α := Set.univ
scoped postfix : max "↑" => S'

scoped syntax (name := dot_prod) "⟨" term ", " term "⟩" : term
macro_rules (kind := dot_prod)
  | `(⟨$x, $y⟩) => `(Euclidean.scalar $x $y)

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

def Rn_prod {n : ℕ} (x y : ℝ^n) : ℝ := ∑ i, x.p i * y.p i

instance {n : ℕ} : Euclidean ℝ^n where
  scalar := Rn_prod
  fg_top := by {
    let ei : Fin n → ℝ^n := i ↦ K_n.canonBasis ℝ i
    rw [Submodule.fg_iff_exists_finite_generating_family]
    use Fin n, Finite.of_fintype (Fin n), ei
    rw [Submodule.eq_top_iff']; intro x
    rw [Submodule.mem_span_range_iff_exists_fun]
    rw [K_n.inCanonBasis x]; use (i ↦ x.p i)
  }

  symm := by {
    intro u v; unfold Rn_prod; congr; ext i; rw [mul_comm]
  }

  add_left := by {
    intro u v w; unfold Rn_prod; rw [←Finset.sum_add_distrib]
    congr; ext i; rw [←add_mul]; rfl
  }

  smul_left := by {
    intro u v k; unfold Rn_prod; rw [Finset.mul_sum]
    congr; simp [HSMul.hSMul, SMul.smul]; ring_nf
  }

  pos := by {
    intro u; unfold Rn_prod; apply Finset.sum_nonneg
    intro i hi; apply mul_self_nonneg
  }

  definie := by {
    intro u; unfold Rn_prod
    rw [Finset.sum_eq_zero_iff_of_nonneg, K_n.eq_zero_iff]
    · apply Iff.intro
      · case mp => intro h i; rw [←mul_self_eq_zero]
                   apply h i; apply Finset.mem_univ
      · case mpr => intro h i hi; rw [h i, mul_zero]
    · intro i hi; apply mul_self_nonneg
  }

end VectorSpace
end TER
