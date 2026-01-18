import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.Complex.Norm
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import «TER Topo».SetElem

-- Préliminaires

def R : Set ℝ := Set.univ

def R_star : Set ℝ := {x : ℝ | x ≠ 0}
notation "Rˣ" => R_star

def R_pos : Set ℝ := {x : ℝ | x ≥ 0}
notation "R₊" => R_pos

def R_neg : Set ℝ := {x : ℝ | x ≤ 0}
notation "R₋" => R_neg

def R_star_pos : Set ℝ := {x : ℝ | x > 0}
notation "R₊ˣ" => R_star_pos

def R_star_neg : Set ℝ := {x : ℝ | x < 0}
notation "R₋ˣ" => R_star_neg

def C : Set ℂ := Set.univ

def C_star : Set ℂ := {x : ℂ | x ≠ 0}
notation "Cˣ" => C_star

notation "ℝ.0" => (0 : ℝ)
notation "ℂ.0" => (0 : ℂ)

-- toute partie non vide majorée admet une borne supérieure:

-- TODO
