import TopoTER.Chapitre1

variable {X : Type*}

open Metrique

lemma diam_pos [EspaceMetrique X] (A : Partie X) : diam A ≥ 0 ∨ diam A = -1 := sorry

lemma diam_crois [EspaceMetrique X] {A : Partie X} {B : Partie X} :
diam_bornee B → A ⊆ B → diam A ≤ diam B := by
  intro bornB A_B
  unfold diam
  dsimp
  split_ifs with hbdd hbd

theorem thm_baire [EspaceMetrique X] (F : ℕ → Partie X) : complet X →
(∀ n : ℕ, F n ≠ ∅ ∧ fermee (F n) ∧ ∀ m : ℕ, m ≥ n → (F (m)) ⊆ (F n)) →
converges_to (fun n ↦ diam (F n)) 0 -> ∃ x : X, ⋂ n : ℕ, F n = {x} := by
  intro compl hFn lim
  have h : ∀ n : ℕ, ∃ x : X, x ∈ F n := fun n ↦ Set.nonempty_iff_ne_empty.mpr (hFn n).1
  choose x hx using h
  have x_cau : cauchy x := by
    intro e e_pos
    let ε := min e 0.5
    have ε_pos : ε > 0 := lt_min e_pos (by norm_num)
    have ε_1 : ε < 1 := lt_of_le_of_lt (min_le_right e 0.5) (by linarith)
    have ε_e : ε ≤ e := min_le_left e 0.5
    rcases lim ε ε_pos with ⟨N, hN⟩
    use N
    intro n hn m hm
    let M : ℕ := min n m
    have hM : M ≥ N := Nat.le_min_of_le_of_le hn hm
    specialize hN M hM
    simp only at hN
    have dfm : diam (F M) ≠ -1 := by
      by_contra heq
      rw [heq] at hN
      have h_d1 : EspaceMetrique.d (-1 : ℝ) 0 = 1 := by
        change |(-1 : ℝ) - 0| = 1
        norm_num
      rw [h_d1] at hN
      linarith
    trans (diam (F M))
    · have Fn_FM : F n ⊆ F M := ((hFn M).2).2 _ (Nat.min_le_left n m)
      have Fm_FM : F m ⊆ F M := ((hFn M).2).2 _ (Nat.min_le_right n m)
      have hn : x n ∈ F M := Set.mem_preimage.mp (Fn_FM (hx n))
      have hm : x m ∈ F M := Set.mem_preimage.mp (Fm_FM (hx m))
      unfold diam at dfm
      dsimp at dfm
      split_ifs at dfm with hbdd
      · unfold diam
        rw [if_pos hbdd]
        apply le_csSup hbdd
        simp only [Set.mem_setOf_eq]
        use (x n)
        constructor
        · exact hn
        · use (x m)
      · contradiction
    · trans ε
      · change |diam (F M) - 0| ≤ ε at hN
        simp at hN
        rcases (diam_pos (F M)) with h | h
        · linarith [abs_le.mp hN]
        · contradiction
      · exact ε_e
  specialize compl x x_cau
  rcases compl with ⟨l, hl⟩
  have lfn : l ∈ ⋂ n : ℕ, F n := sorry
  have hdiam : ∀ m : ℕ, diam (⋂ n : ℕ, F n) ≤ diam (F m) := by
    intro m
    apply diam_crois
    --exact Set.iInter_subset_of_subset m fun ⦃a⦄ a_1 ↦ a_1
    sorry
  have diam_0 : diam (⋂ n : ℕ, F n) = 0 := sorry
  sorry
