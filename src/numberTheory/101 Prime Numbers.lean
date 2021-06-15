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

example : 7 ∣ 91 := begin use 13, tauto end
example : (-5 : ℤ) ∣ 45 := begin use -9, tauto end
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

theorem prime_fact (n : ℕ) (H: 1 < n) : ∃ p, prime p → p ∣ n := begin
  induction n with k hk,
    use 2,
    intro h,
    use 0, simp,
    
    
    sorry
    -- # Add strong induction proof from notes
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

theorem prime_or_product (n : ℕ) (H : n > 1) : prime n ∨ sorry /- finite sequence of primes -/ :=
begin
  sorry, -- # Add strong induction proof from notes
end

/-
## Theorem 1.8
Let n have the prime factorisations
      n = p₁ × ... × p_r = q₁ × ... × q_s
Then every prime occurs equally often in both factorisations (and so r = s)
-/

-- # No clue how to put this into code


