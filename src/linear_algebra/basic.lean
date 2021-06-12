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

variables [field F] [add_comm_group V] [vector_space F V] (u v w : V) (a b c : F)

open vector_space

lemma zero_smul' (u : V) : (0 : V) = (0 : F) • u :=
begin
  sorry
end

lemma smul_zero'' (u : V) : a • (0 : V) = (0 : V) :=
begin
  sorry
end

lemma inv_eq_neg (u : V) (x : F) : -u = (-1 : F) • u :=
begin
  sorry
end
