import Mathlib.Data.Set.Basic

variable {α : Type u}
variable {S : Set α}

@[coe] def coe_type : α → @Set.univ α := fun e => ⟨e, Set.mem_univ e⟩
@[simp, norm_cast] lemma coe_coe_type (e : α) : ↑(coe_type e) = e := by rfl

instance [HAdd α α α] : HAdd S S α where
  hAdd := fun x => fun y => (x : α) + (y : α)

instance [HSub α α α] : HSub S S α where
  hSub := fun x => fun y => (x : α) - (y : α)

instance [HMul α α α] : HMul S S α where
  hMul := fun x => fun y => (x : α) * (y : α)

instance [HDiv α α α] : HDiv S S α where
  hDiv := fun x => fun y => (x : α) / (y : α)

syntax (name := setfun) term " ↦ " term : term
macro_rules (kind := setfun)
  | `($x ↦ $desc) => `(fun $x => coe_type $desc)

variable {x y z : S}

@[simp] lemma elem_eq : x = y ↔ x.val = y.val := by rw [SetCoe.ext_iff]

@[simp] lemma elem_le [LE α] : x ≤ y ↔ x.val ≤ y.val := by rfl

@[simp] lemma elem_lt [LT α] : x < y ↔ x.val < y.val := by rfl

@[simp] lemma elem_add [HAdd α α α] : (@HAdd.hAdd S S α) x y = x.val + y.val := by rfl

@[simp] lemma elem_sub [HSub α α α] : (@HSub.hSub S S α) x y = x.val - y.val := by rfl

@[simp] lemma elem_mul [HMul α α α] : (@HMul.hMul S S α) x y = x.val * y.val := by rfl

@[simp] lemma elem_div [HDiv α α α] : (@HDiv.hDiv S S α) x y = x.val / y.val := by rfl

-- une version du simplificateur restreinte aux lemmes définies ici:
syntax (name := cleanup) "cleanup" : tactic
macro_rules (kind := cleanup)
  | `(tactic| cleanup) => `(tactic| simp only [coe_type, elem_eq, elem_le, elem_lt,
                                               elem_add, elem_sub, elem_mul, elem_div])
