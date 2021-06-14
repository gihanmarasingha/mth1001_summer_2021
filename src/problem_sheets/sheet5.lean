import linearAlgebra.basic

-- initiating the file
universes u v
variables {F : Type u} {V : Type v}
variables [field F] [add_comm_group V] [vector_space F V] (u v w : V) (a b c : F)

open vector_space

-- Let's define some basic results we are going to need, these are from our
-- definition of a vector space,

lemma left_dist (a : F) (u v : V) : a • ( u + v ) = a • u + a • v := left_dist a u v
lemma right_dist (a b : F) (u : V) : (a + b) • u = a • u + b • u := right_dist a b u
lemma smul_smul' (a b : F) (u : V) : a • (b • u) = (a * b) • u := smul_smul a b u
lemma smul_id (u : V) : (1 : F) • u = u := smul_id u

section question1

/- Prove the fact that 0 • u = 0, where 0 is the zero vector  -/
lemma zero_smul' (u : V) : (0 : V) = (0 : F) • u :=
begin
  sorry
end

end question1

section question2

/- Question 2. What about the other way? -/
lemma smul_zero'' (u : V) : a • (0 : V) = (0 : V) :=
begin
  sorry
end

end question2

section question3

/- Question 3. This one is slightly harder, try to prove that -u is just -1 • u -/
lemma inv_eq_neg (u : V) (x : F) : -u = (-1 : F) • u :=
begin
  sorry
end

end question3
