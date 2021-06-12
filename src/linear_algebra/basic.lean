import data.real.basic tactic

universes u v
variables {F : Type u} {V : Type v}

/-
  These are the notes that I wrote for ECM2903 Linear Algebra, but they define all
  of the necessary stuff. Firstly, a vector space,
-/

class vector_space (F : Type u) (V : Type v) [field F] [add_comm_group V] extends has_scalar F V :=
(left_dist : ∀ (a : F) (u v : V), a • ( u + v ) = a • u + a • v)
(right_dist : ∀ (a b : F) (u : V), (a + b) • u = a • u + b • u)
(smul_smul : ∀ (a b : F) (u : V), a • (b • u) = (a * b) • u)
(smul_id : ∀ (u : V), (1 : F) • u = u)


/-
  Now we to define what we are working on, so let us define a field, an additive
  abelian group (a group thats additive and commutative) and then a vector space.
  Now, three elements of the vectorspace `u`, `v` and `w` and then `a`, `b` and `c`
  elements of a field.
-/
variables [field F] [add_comm_group V] [vector_space F V] (u v w : V) (a b c : F)

open vector_space


/- Now prove the fact that 0 • u = 0, where 0 is the zero vector  -/
lemma zero_smul' (u : V) : (0 : V) = (0 : F) • u :=
begin
  sorry
end

/- What about the other way? -/
lemma smul_zero'' (u : V) : a • (0 : V) = (0 : V) :=
begin
  sorry
end

/- This one is slightly harder, try to prove that -u is just -1 • u -/
lemma inv_eq_neg (u : V) (x : F) : -u = (-1 : F) • u :=
begin
  sorry
end
