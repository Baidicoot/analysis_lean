namespace real

universe u
constant ℝ : Type u
constants zero one : ℝ
constant neg : ℝ -> ℝ
constants add mul : ℝ -> ℝ -> ℝ
constant lt : ℝ -> ℝ -> Prop
constant mul_inv : ℝ -> ℝ.

noncomputable instance : has_lt ℝ := ⟨lt⟩
instance : has_le ℝ :=
    ⟨λx y, x < y ∨ x = y⟩
noncomputable instance : has_add ℝ := ⟨add⟩
noncomputable instance : has_mul ℝ := ⟨mul⟩
noncomputable instance : has_zero ℝ := ⟨zero⟩
noncomputable instance : has_one ℝ := ⟨one⟩
noncomputable instance : has_neg ℝ := ⟨neg⟩
noncomputable instance : has_sub ℝ :=
    ⟨λx y, x + -y⟩
noncomputable instance : has_inv ℝ := ⟨mul_inv⟩
noncomputable instance : has_div ℝ :=
    ⟨λx y, x * y⁻¹⟩

axiom mul_comm {x y : ℝ} :
    x * y = y * x
axiom mul_assoc {x y z : ℝ} :
    x * (y * z) = (x * y) * z

axiom add_comm {x y : ℝ} :
    x + y = y + x
axiom add_assoc {x y z : ℝ} :
    x + (y + z) = (x + y) + z

axiom zero_add_identity {x : ℝ} :
    0 + x = x
axiom one_mul_identity {x : ℝ} :
    1 * x = x

axiom neg_add_zero {x : ℝ} :
    -x + x = 0
axiom inv_mult_one {x : ℝ} {h : x ≠ 0} :
    x * x⁻¹ = 1

axiom left_distrib {x y z : ℝ} :
    x * (y + z) = x * y + x * z

axiom lt_trans {x y z : ℝ} :
    x < y -> y < z -> x < z
axiom lt_iff_le_not_le {x y : ℝ} :
    x < y <-> x ≤ y ∧ ¬y ≤ x

axiom completeness
    {A : set ℝ} {c : ℝ}
    {c_is_ub : ∀x ∈ A, x ≤ c} :
    ∃l, (∀x ∈ A, x ≤ l) ∧ (∀u, (∀x ∈ A, x ≤ c) -> l ≤ u)

-- example proofs of basic results

lemma add_zero_identity {x : ℝ} : x + 0 = x :=
begin
    rw add_comm,
    exact zero_add_identity,
end

lemma mul_one_identity {x : ℝ} : x * 1 = x :=
begin
    rw mul_comm,
    exact one_mul_identity,
end

lemma right_distrib {x y z : ℝ} :
    (y + z) * x = y * x + z * x :=
begin
    rw mul_comm,
    rw left_distrib,
    rw @mul_comm y x,
    rw @mul_comm z x,
end

lemma leq_refl {x : ℝ} :
    x ≤ x :=
begin
    right,
    reflexivity,
end

lemma leq_trans {x y z : ℝ} :
    x ≤ y -> y ≤ z -> x ≤ z :=
begin
    intros h0 h1,
    cases h0,
    {
        cases h1,
        {
            left,
            apply @lt_trans x y z,
            assumption, assumption,
        },
        {
            left,
            rw <- h1,
            exact h0,
        },
    },
    {
        cases h1,
        {
            
        }
    },
end