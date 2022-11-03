import algebra.order.field_defs

universe u
constant ℝ : Type u

axiom reals_lin_ord_field : linear_ordered_field ℝ

noncomputable instance : linear_ordered_field ℝ :=
  reals_lin_ord_field

noncomputable instance : has_zero ℝ := ⟨linear_ordered_field.zero⟩
noncomputable instance : has_one ℝ := ⟨linear_ordered_field.one⟩
noncomputable instance : has_add ℝ := ⟨linear_ordered_field.add⟩
noncomputable instance : has_neg ℝ := ⟨linear_ordered_field.neg⟩
noncomputable instance : has_mul ℝ := ⟨linear_ordered_field.mul⟩
noncomputable instance : has_inv ℝ := ⟨linear_ordered_field.inv⟩
instance : has_lt ℝ := ⟨linear_ordered_field.lt⟩
instance : has_le ℝ := ⟨linear_ordered_field.le⟩

axiom reals_complete :
  ∀X : set ℝ, ∃c : ℝ, (∀x ∈ X, x ≤ c)
    ∧ (∀u : ℝ, (∀x ∈ X, x ≤ u) -> c ≤ u)

example {x : ℝ} : x * 0 = 0 := sorry