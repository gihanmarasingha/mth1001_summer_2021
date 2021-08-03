import data.real.basic algebra.module.submodule algebra.module.submodule_lattice

-- initiating the file
universes u v
variables {F : Type u} {V : Type v}
variables [field F] [add_comm_group V] [module F V] (u v w : V) (a b c : F)

open real module

-- Let's define some basic results we are going to need, these are from our
-- definition of a vector space,

/- lemma left_dist (a : F) (u v : V) : a • ( u + v ) = a • u + a • v := left_dist a u v
lemma right_dist (a b : F) (u : V) : (a + b) • u = a • u + b • u := right_dist a b u
lemma smul_smul' (a b : F) (u : V) : a • (b • u) = (a * b) • u := smul_smul a b u
lemma smul_id (u : V) : (1 : F) • u = u := smul_id u -/


section question1

  /- Prove the fact that 0 • u = 0, where 0 is the zero vector  -/
  lemma zero_smul' (u : V) : (0 : V) = (0 : F) • u :=
  begin
    symmetry,
    rw ← add_zero ((0 : F) • u),
    rw ← add_right_cancel_iff,                -- 0 • u + (0 • u + (- 0 • u)) = 0 • u + (- 0 • u)
    swap, exact (0 : F) • u + ((- 0 : F) • u),
    rw [zero_add, add_zero],
    rw ← add_assoc,                           -- (0 • u + 0 • u) + (- 0 • u) = 0 • u + (- 0 • u)
    rw add_right_cancel_iff,                                -- 0 • u + 0 • u = 0 • u
    rw ← add_smul (0 : F) (0 : F) u,                         -- (0 + 0) • u = 0 • u
    rw add_zero,                                                    -- 0 • u = 0 • u
  end

  /- What about the other way? -/
  lemma smul_zero'' (u : V) : a • (0 : V) = (0 : V) :=
  begin
    have h : a • (0 : V) = a • 0 + a • 0, from
    calc a • (0 : V) = a • (0 + 0) : by rw add_zero 
    ... = a • 0 + a • 0 : by rw smul_add,
    rw ← add_right_cancel_iff at h, swap,
    exact - (a • 0),
    rw add_neg_self at h,
    rw add_assoc at h,
    rw add_neg_self at h,
    rw add_zero at h,
    rw ← h,
  end

  /- This one is slightly harder, try to prove that -u is just -1 • u -/
  lemma inv_eq_neg (u : V) (x : F) : -u = (-1 : F) • u :=
  begin
    have h : (-1 : F) • u = (-1 : F) • u + (0 : V), by rw add_zero,
    rw ← @add_neg_self _ _ u at h,
    rw ← add_assoc at h,
    have h₁ : (-1 : F) • u + u + -u = (-1 : F) • u + (1 : F) • u + -u, by sorry,
    rw h₁ at h,
    rw ← add_smul (-1 : F) (1 : F) u at h,
    rw neg_add_self at h,
    rw ← zero_smul' at h,
    rw zero_add at h,
    rw ← h,
  end
end question1

def R_n_module (n : ℕ) : module ℝ (fin n → ℝ) := 
  { smul := λ x hx a, x * (hx a),
  one_smul := λ b, by simp,
  mul_smul := λ x y b, by {simp, ext, linarith,},
  smul_add := λ r x y, by {ext, dsimp, linarith,},
  smul_zero := λ r, by {ext, dsimp, linarith,},
  add_smul := λ r s x, by {ext, dsimp, linarith,},
  zero_smul := λ r, by {ext, dsimp, linarith,},
}

section question2

  def W₃ : submodule ℝ (R_n_module 3) := { 
    carrier := U.carrier ∩ W.carrier,
    zero_mem' := by simp,
    add_mem' := by simp [add_mem] {contextual := tt},
    smul_mem' := by simp [smul_mem] {contextual := tt},}
  
end question2


section question3

end question3


section question4

  /-
  Let V be a vector space over K and let U, W be subspaces of V . Show
  that U ∩ W and {u + w : u ∈ U, w ∈ W} are subspaces of V .
  -/

end question4

