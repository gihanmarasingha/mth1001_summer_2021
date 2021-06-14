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
