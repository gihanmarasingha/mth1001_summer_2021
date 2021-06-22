import data.int.basic data.nat.basic data.nat.prime tactic

open int nat


/- 
## Definition 1.1
A prime number is a natural number p > 1, which is divisible only
by the natural numbers 1 and p.
-/


/-
## Definition 1.2
Let m, n ∈ ℤ.
Then n is divisible by m (m ∣ n) if there exists a ∈ ℤ such that n = ma.
-/
example : 7 ∣ 91 := by {use 13, tauto}

example : (-5 : ℤ) ∣ 45 := by {use -9, tauto}

example : ¬ (11 ∣ 87) := begin
  have h₁ : 11 ≠ 3 := by norm_num, --
  have h₂ : 11 ≠ 29 := by norm_num,
  have h₃ : 87 = 3 * 29 := by norm_num,

  intro h,

  rw [← coprime_primes, prime.coprime_iff_not_dvd (show prime 11, by norm_num)] at h₁ h₂, repeat {norm_num},
  rw [h₃, prime.dvd_mul] at h,

  cases h with k₁ k₂,
  repeat {contradiction},
  norm_num,
end

example : ∀ x : ℤ, 1 ∣ x := begin -- Every number is dvisible by 1.
  intro x,
  use x, 
  simp, 
end

example (x : ℤ) : 2 ∣ x ↔ even x := begin -- A number is divisible by 2 iff it is even.
  split,
   repeat {intro h, 
           cases h with k hk,
           use k, 
           exact hk},
end


/-
## Theorem 1.4
Let n : ℕ with n > 1.
Then n has a prime factor p.
-/
theorem prime_fact : ∀ n : ℕ, 2 ≤ n → ∃ p, prime p → p ∣ n := begin
  intro n,
  apply nat.strong_induction_on n,

  intros a h₁ ha,
  by_cases prime a,
    {use a, tauto},

    {unfold prime at h, push_neg at h,
    specialize h ha,
    rcases h with ⟨m, hm, h₁, h₂⟩,
    use m, tauto}
end


/-
## Theorem 1.5 - Euclid
There are infinitely many primes.
-/
theorem Euclid : ∀ N, ∃ p ≥ N, prime p := begin
  intro N,

  let M := factorial N + 1,
  let p := min_fac M,

  have hp : prime p := 
    begin
      refine min_fac_prime _,
      have : factorial N > 0 := factorial_pos N,
      linarith,
  end,

  use p,
  split,
   {by_contradiction H,
    have h₁ : p ∣ factorial N + 1 := min_fac_dvd M,
    have h₂ : p ∣ factorial N :=
      begin
        refine hp.dvd_factorial.mpr _,
        exact le_of_not_ge H,
    end,
    have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁,
    
    exact prime.not_dvd_one hp h},
   {exact hp},
end

/-
## Theorem 1.7
If n : ℕ, with n > 1, then either n is prime, or is a product of a
(finite) sequence of primes.
-/
theorem prime_or_product_1 (n : ℕ) (H : 2 ≤ n) : prime n ∨ ∃ m a: ℕ, 2 ≤ m ∧ m < n → m * a = n :=
-- Either prime n or n is product of 2 different naturals
begin
  by_cases prime n,
    {left, exact h},
    {right, unfold prime at h, push_neg at h,
      specialize h H,
      cases h with m hm,

      use m,
      use n/m,
      intro h₁,
      cases hm with h₂ h₃,
      exact nat.mul_div_cancel' h₂,
    }
end

def list_prod : list ℕ → ℕ
  | [] := 1
  | (h :: t) := h * list_prod t

def list_prime : list ℕ → Prop
  | [] := true
  | (h :: t) := prime h ∧ list_prime t

def list_prod_prime_eq (n : ℕ) (P : list ℕ): Prop :=
  list_prime P ∧ n = list_prod P

theorem prime_or_product_2 (n : ℕ) (H : 2 ≤ n): ∃ P : list ℕ, list_prod_prime_eq n P := begin
  -- n is a product of a list of primes
  sorry,
end

/-
## Theorem 1.8
Let n have the prime factorisations
      n = p₁ × ... × p_r = q₁ × ... × q_s
Then every prime occurs equally often in both factorisations (and so r = s)
-/

-- # No clue how to put this into code


