import «TER Topo».Préliminaires

-- 1. Espaces métriques

namespace Metric

variable {α : Type u}
variable {X : Set α}

-- 1.1. Définition, premiers exemples

-- Définition 1.1.

def sep (d : X × X → R₊) : Prop := ∀ x y, d (x, y) = ℝ.0 ↔ x = y

def symm (d : X × X → R₊) : Prop := ∀ x y, d (x, y) = d (y, x)

def ineq (d : X × X → R₊) : Prop := ∀ x y z, d (x, y) + d (y, z) ≥ d (x, z)

def isDistance (d : X × X → R₊) : Prop := sep d ∧ symm d ∧ ineq d

structure MetricSpace (α : Type) where
  X : Set α
  d : X × X → R₊
  is_dist : isDistance d

-- un constructeur plus pratique à utiliser:

structure newMetricSpace (α : Type) extends MetricSpace α where
  dist : X × X → R
  dist_pos : ∀ x y, dist (x, y) ≥ ℝ.0
  d := fun (x, y) => ⟨dist (x, y), dist_pos x y⟩

  dist_sep : sep d
  dist_symm : symm d
  dist_ineq : ineq d
  is_dist := And.intro dist_sep (And.intro dist_symm dist_ineq)

-- Exemple 1.2.

-- 1.
def R_usuelle : newMetricSpace ℝ where
  X := R
  dist := (x, y) ↦ |x - y|
  dist_pos := by intro x y; exact abs_nonneg (x - y)

  dist_sep := by {
    intro x y; cleanup; rw [abs_eq_zero, sub_eq_zero]
  }

  dist_symm := by {
    intro x y; cleanup; rw [abs_sub_comm]
  }

  dist_ineq := by {
    intro x y z; cleanup; apply abs_sub_le
  }

-- 2.
def C_usuelle : newMetricSpace ℂ where
  X := C
  dist := (x, y) ↦ ‖x - y‖
  dist_pos := by intro x y; apply Real.sqrt_nonneg

  dist_sep := by {
    intro x y; cleanup; rw [norm_eq_zero, sub_eq_zero]
  }

  dist_symm := by {
    intro x y; cleanup; rw [norm_sub_rev]
  }

  dist_ineq := by sorry --TODO

end Metric
