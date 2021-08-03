import data.real.basic tactic data.set.basic

universes u v
variables (F : Type u) (V : Type v)
variables [semiring F] [add_comm_group V]

/-
  These are the notes that I wrote for ECM2903 Linear Algebra, but they define all
  of the necessary stuff. Firstly, a vector space,
-/

class vector_space extends has_scalar F V :=
(left_dist : ∀ (a : F) (u v : V), a • ( u + v ) = a • u + a • v)
(right_dist : ∀ (a b : F) (u : V), (a + b) • u = a • u + b • u)
(smul_smul : ∀ (a b : F) (u : V), a • (b • u) = (a * b) • u)
(smul_id : ∀ (u : V), (1 : F) • u = u)
(smul_add : ∀ (a : F) (u v : V), a • (u + v) = a • u + a • v)
(add_smul : ∀ (a b : F) (u : V), (a + b) • u = a • u + b • u)


/-
  Now we to define what we are working on, so let us define a field, an additive
  abelian group (a group thats additive and commutative) and then a vector space.
  Now, three elements of the vectorspace `u`, `v` and `w` and then `a`, `b` and `c`
  elements of a field.
-/
variables [field F] [add_comm_group V] [vector_space F V] (u v w : V) (a b c : F)

open vector_space

structure subSpace : Type v :=
  (carrier : set V)
  (zero_mem' : (0 : V) ∈ carrier)
  (add_mem' : ∀ {a b : V}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
  (smul_mem' : ∀ (c_1 : F) {x : V}, x ∈ carrier → c_1 • x ∈ carrier)



variables {p q : subSpace F V}
variables (p q)

@[simp] lemma zero_mem : (0 : V) ∈ p.carrier := p.zero_mem'
@[simp] lemma add_mem (u v : V) (hu : u ∈ p.carrier) (hv : v ∈ p.carrier) : u + v ∈ p.carrier := p.add_mem' hu hv
@[simp] lemma smul_mem (a : F) (u : V) (hu : u ∈ p.carrier): a • u ∈ p.carrier := p.smul_mem' a hu

def Has_Inf (U W : subSpace F V) : subSpace F V := { 
  carrier := U.carrier ∩ W.carrier,
  zero_mem' := begin
    split,
      { exact U.zero_mem'},
      { exact W.zero_mem'},
  end,
  add_mem' := begin
    intros a b ha hb, 
    cases ha with aU aW,
    cases hb with bU bW,
    split,
      { exact U.add_mem' aU bU},
      { exact W.add_mem' aW bW}
  end,
  smul_mem' := begin
    intros c x hx,
    split,
      { exact U.smul_mem' c hx.left},
      { exact W.smul_mem' c hx.right}
  end }

def Has_Inf' (U W : subSpace F V) : subSpace F V := { 
  carrier := U.carrier ∩ W.carrier,
  zero_mem' := by simp,
  add_mem' := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt},}

instance : has_inf (subSpace F V) :=
⟨λ p q, {
  carrier := p.carrier ∩ q.carrier,
  zero_mem' := by simp,
  add_mem'  := by simp [add_mem] {contextual := tt},
  smul_mem' := by simp [smul_mem] {contextual := tt} }⟩
