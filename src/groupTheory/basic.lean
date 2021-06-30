import algebra.group group_theory.order_of_element
import data.nat.parity
/-!
# Group theory basics (drawn from Sheet 1 of the MTH2010 Groups, Rings, and Fields module)
-/

/-!
## Commutative groups
-/

def is_comm (G : Type) [group G] : Prop := ∀ g h : G, g * h = h * g

variables {G H : Type} [group G] [group H]

/--
Prove that a product `G × H` of groups is commutatitive if and only if each of `G` and `H` are.
-/
lemma commutative_prod_iff : is_comm (G × H) ↔ (is_comm G) ∧ (is_comm H) :=
sorry

/-!
## Group orders

Let `G` be a group and let `x : G`. We write `order_of x` for the order of `x` in `G`.

Useful theorems regarding group orders:

1. `pow_order_of_eq_one x` states that `x` raised to the power `order_of x` equals
the identity element in the group. That is, `x ^ order_of x = 1`.

2. `order_of_dvd_of_pow_eq_one` states that if `x ^ n = 1`, then `order_of x ∣ n`.

3. `nat.dvd_antisymm` is the result that if `n ∣ m` and `m ∣ n`, then `n = m`. This is useful for
proving `order_of y = z` as it reduces the problem to proving `order_of y ∣ z` and `z ∣ order_of y`.

4. `pow mul a m n` states `a ^ (m * n) = (a ^ m) ^ n`.

5. `nat.mul_dvd_mul_iff_left` states that if `0 < a`, then `a * b ∣ a * c ↔ b ∣ c`.

6. `inv_pow a n` states that `a⁻¹ ^ n = (a ^ n)⁻¹`.

7. `one_inv` states that `1⁻¹ = 1`.

8. `inv_inv a` states that `(a⁻¹)⁻¹ = a`.

9. `conj_pow` states that `(a * b * a⁻¹) ^ i = a * (b ^ i) * a⁻¹`.

-/

lemma order_of_pow_of_order_of_eq_mul 
  (x : G) (s t : ℕ) (h : order_of x = s * t) (hspos : s > 0) (htpos : t > 0) :
  order_of (x ^ s) = t :=
sorry

lemma order_of_inv (x : G) : order_of x⁻¹ = order_of x :=
sorry

lemma order_of_conj (x y : G) : order_of x = order_of (y * x * y⁻¹) :=
sorry

lemma order_comm (a b : G) : order_of (a * b) = order_of (b * a) :=
sorry

open_locale classical

lemma exists_even_order_of_of_even_card [fintype G] (h : even (fintype.card G)) :
  ∃ x : G, even (order_of x) := sorry


