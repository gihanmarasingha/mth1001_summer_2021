import data.int.basic data.nat.basic data.nat.prime tactic algebra.floor

open int nat


section prime_numbers_and_divisibility
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
  theorem prime_fact' : ∀ n : ℕ, 2 ≤ n → ∃ p, prime p → p ∣ n + 1 := begin
    intros n hn,
    use 0,
    intro hp,
    cases hp with k hk,
    linarith,
  end

  theorem prime_fact : ∀ n : ℕ, 2 ≤ n → ∃ p, prime p ∧ p ∣ n := begin
    intro n,
    apply nat.strong_induction_on n,

    intros a h₁ ha,
    by_cases prime a,
      {use a, tauto},

      {unfold prime at h, push_neg at h,
      specialize h ha,
      rcases h with ⟨m, hm, h₁, h₂⟩,
      use m, sorry}
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
  theorem prime_or_product_1 (n : ℕ) (H : 2 ≤ n) : prime n ∨ ∃ m a: ℕ, 2 ≤ m ∧ m < n ∧ m * a = n := begin
    -- Either prime n or n is product of 2 different naturals
    by_cases prime n,
      {left, exact h},
      {right, unfold prime at h, push_neg at h,
        specialize h H,
        cases h with m hm,

        use m,
        use n/m,
        rcases hm with ⟨h₂, h₃, h₄⟩,
        split,
          { sorry,},
          sorry,
      }
  end


  def list_prod : list ℕ → ℕ
    | [] := 1
    | (h :: t) := h * list_prod t

  #eval list_prod [2, 5, 7, 10]


  def list_prime : list ℕ → Prop
    | [] := true
    | (h :: t) := prime h ∧ list_prime t

  lemma list_prime_2_3_5 : list_prime [2, 3, 5] := begin
    split, norm_num,
    split, norm_num,
    split, norm_num,
    triv,
  end


  def list_prod_prime_eq (n : ℕ) (P : list ℕ): Prop :=
    list_prime P ∧ n = list_prod P

  example : list_prod_prime_eq 30 [2,3,5] := begin
    split, exact list_prime_2_3_5,
    dsimp [list_prod],
    norm_num,
  end


  theorem list_prime_append (P Q : list ℕ) (H : list_prime P) (G : list_prime Q) : list_prime (P ++ Q) := begin
    sorry,
  end


  theorem list_prod_append (P Q : list ℕ) : list_prod P * list_prod Q = list_prod (P ++ Q) := begin
    sorry,
  end


  theorem prime_or_product_2 (n : ℕ): 2 ≤ n → ∃ P : list ℕ, list_prod_prime_eq n P := begin
    -- n is a product of a list of primes
    apply nat.strong_induction_on n,
    intros a ha ha₂,
    have h := prime_or_product_1 a ha₂,

    cases h with h₁ h₂,
    { use ([a]),
      split,
      { dsimp [list_prime],
        tauto},
      { dsimp [list_prod],
        norm_num}
    },
    { rcases h₂ with ⟨b, c, hb⟩,
      rcases hb with ⟨kb₁, kb₂, kabc⟩,
      
      have Hb := ha b kb₂ kb₁,
      have Hc := ha c,
      have kc₁ : 1 < c, begin
        rw [← kabc, ← mul_one b, mul_assoc, one_mul, mul_lt_mul_left (show 0 < b, by linarith)] at kb₂,
          exact kb₂,
      end,
      have kc₂ : c < a, begin
        by_contra kca,
          push_neg at kca,
          rw [← kabc, mul_le_iff_le_one_left] at kca;
            linarith,
      end,
      
      specialize Hc kc₂ kc₁,
      rcases Hb with ⟨Q, primeQ, prodQb⟩,
      rcases Hc with ⟨R, primeR, prodRc⟩,
      
      use Q ++ R,
      split,
      { exact list_prime_append Q R primeQ primeR,},
      { rw [← kabc, prodQb, prodRc],
        exact list_prod_append Q R}
    }
    
  end

  theorem prime_or_product_3 (n : ℕ): 2 ≤ n → ∃ P : list ℕ, list_prod_prime_eq n P := begin
    apply nat.strong_induction_on n,
    intros k hk h2k,

    by_cases prime k,
    { use ([k]),
      dsimp [list_prod_prime_eq],
      split,
        { split,
            exact h,
            triv,},
        { dsimp [list_prod],
          norm_num,}},
    { have h := prime_fact k h2k,
      rcases h with ⟨p, hp₁, hp₂⟩,
      cases hp₂ with c hc,

      specialize hk c,
      
      have c_le_k : c < k := begin
        by_contra kc,
          push_neg at kc,
          rw [hc, mul_le_iff_le_one_left] at kc,
            { cases hp₁ with hp₂ hp₃,
              linarith,},
            { linarith,}
      end,
      have c_ge_2 : 2 ≤ c := begin
        sorry,
      end,

      specialize hk c_le_k c_ge_2,
      cases hk with Q hcQ,

      dsimp [list_prod_prime_eq] at hcQ,
      cases hcQ with Qprime Qprodc,

      use ([p] ++ Q),
      dsimp [list_prod_prime_eq],
      split,
      { split,
        { exact hp₁},
        { exact Qprime}},
      { rw [hc, Qprodc],
        dsimp [list_prod],
        refl,}
      }

  end

  #check le_mul_of_pos_right
  #check mul_lt_mul_left



  /-
  ## Theorem 1.8
  Let n have the prime factorisations
        n = p₁ × ... × p_r = q₁ × ... × q_s
  Then every prime occurs equally often in both factorisations (and so r = s)

  This is what we are working up to proving, but we will first need modular arithmetic
  -/

end prime_numbers_and_divisibility

section modular_arithmetic
  /-
  ## Definition 1.9
  For an integer n ≥ 1, we say that integers a and b are congruent modulo n, 
  whenever (a − b)/n is an integer. 
  -/
  
  def congModN (a b : ℤ) (n : ℕ) := ∃ m : ℤ, (a - b) = m * n
  def congModNInt (a b n : ℤ) := ∃ m : ℤ, (a - b) = m * n

  /-
  ## Theorem 1.10
  Congruence behaves like an equivalence relation, i.e. it satisfies
    Reflexivity
    Symmetry
    Transitivity
  -/

  theorem cong_refl (a : ℤ) (n : ℕ): congModN a a n := begin
    dsimp [congModN],
    use 0,
    simp,
  end

  theorem cong_symm (a b : ℤ) (n : ℕ): congModN a b n ↔ congModN b a n := begin
    split;
      { intro h,
        cases h with m hm,
        use (-m),
        linarith},
  end

  theorem cong_trans (a b c : ℤ) (n : ℕ) (H₁ : congModN a b n) (H₂ : congModN b c n): congModN a c n := begin
      cases H₁ with m hm,
      cases H₂ with p hp,
      
      use (m + p),
      rw [add_mul, ← hm, ← hp],
      linarith,
  end


  /-
  ## Theorem 1.11
  Congruence preserves addition, subtraction and multiplication
  -/

  theorem cong_add (a b c d : ℤ) (n : ℕ) (H₁ : congModN a b n) (H₂ : congModN c d n): congModN (a + c) (b + d) n := begin
    cases H₁ with m hm,
    cases H₂ with p hp,

    use (m + p),
    rw [add_mul, ← hm, ← hp],
    linarith,
  end

  theorem cong_sub (a b c d : ℤ) (n : ℕ) (H₁ : congModN a b n) (H₂ : congModN c d n): congModN (a - c) (b - d) n := begin
    cases H₁ with m hm,
    cases H₂ with p hp,

    use (m - p),
    rw [sub_mul, ← hm, ← hp],
    linarith,   
  end

  theorem cong_mul (a b c d : ℤ) (n : ℕ) (H₁ : congModN a b n) (H₂ : congModN c d n): congModN (a * c) (b * d) n := begin
    cases H₁ with m hm,
    cases H₂ with p hp,

    use (b*p + c*m),
    rw add_mul,
    rw [mul_assoc b p n, ← hp, mul_assoc c m n, ← hm, mul_sub, mul_sub],
    linarith,
  end


  /-
  ## Remark 1.12
  We must be careful with division, i.e.
  a/c is not always congruent to b/d (mod n)
  -/


  /-
  ## Theorem 1.13
  Let n ≥ 1 and a ∈ Z. There are unique q ∈ Z and r ∈ {0, 1, . . . , n − 1}, 
  with a = qn + r.
  (We call q the quotient and r the remainder obtained by dividing a by n.)
  -/

  theorem quot_rem (a: ℤ) (n : ℕ) (H₁ : 1 ≤ n) : ∃ q r : ℤ, 0 ≤ r → r ≤ n - 1 → a = q*n + r := begin
    let q := floor (a/n),
    use q,
    use (a - q*n),
    intros h₁ h₂,
    linarith,
  end

  theorem quot_rem_unique (a : ℤ) (n : ℕ) (H₁ : 1 ≤ n) : ∃! q r : ℤ, 0 ≤ r → r ≤ n - 1 → a = q*n + r := begin
    rw exists_unique,
    let q := floor (a/n),
    have hqa₁ : q ≤ a/n := begin
      dsimp [q],
      tauto,
    end,
    have hqa₂ : (a/n) ≤ ceil (a/n) := begin
      sorry,
    end,
    have hqa₃ : ceil (a/n) ≤ q + 1 := begin
      dsimp [q],
      exact ceil_le_floor_add_one (a/n),
    end,
    have hqa₄ : a/n ≤ q + 1 := begin
      exact le_trans hqa₂ hqa₃,
    end,
    clear hqa₃ hqa₄,
    use q,
    split,
      { rw exists_unique,
        use (a - q * n),
        split,
          { intros h₁ h₂,
            linarith,},
          { intros r hr₁,
            sorry},
      },
      {sorry}
  end
  #check nat.mod_add_div

  lemma mod_le_n (a n : ℕ) (H₁ : 1 ≤ n) : a % n ≤ n := begin
    induction a with k hk,
      { rw nat.zero_mod,
        linarith,},
      { rw succ_eq_add_one,
        rw nat.add_mod,
        by_cases n = 1,
          { -- For n = 1
            rw h,
            simp,},
          { -- For n ≠ 1, i.e. 1 < n
            have h₂ : 1 < n := by sorry,}}
  end

  theorem quot_rem_nat (a n : ℕ) (H₁ : 1 ≤ n) : ∃ q r : ℕ, 0 ≤ r ∧ r ≤ n - 1 ∧ a = q*n + r := begin
    use a/n,
    use a % n,
    split,
      { exact nat.zero_le (a % n)},
      { split,
        { sorry},
        { sorry}}
  end

  theorem quot_rem_nat' (a n : ℕ) : ∃ q r : ℕ, 0 ≤ r ∧ r ≤ n ∧ a = q * (n + 1) - q + r := begin
    use a/n,
    use a % n,
    split,
      { exact nat.zero_le (a % n),},
      { split,
        { exact mod_le_n a n},
        { rw mul_add,
          rw mul_one,
          simp,
          have h₁ : a / n * n ≥ a - n := begin
            sorry,
          end,
          have h₂ := mod_le_n a n,
          sorry,}}
  end
-- a ≤ a < a - n

  theorem quot_rem_unique' (a n q₁ q₂ r₁ r₂ : ℤ) (H₁ : 1 ≤ n) 
    (H1r₁ : 0 ≤ r₁) (H2r₁ : r₁ < n) 
    (H1r₂ : 0 ≤ r₂) (H2r₂ : r₂ < n) 
    (Ha₁ : a = q₁ * n + r₁) (Ha₂ : a = q₂ * n + r₂): r₁ = r₂ ∧ q₁ = q₂ := begin
      split,
        { have h₁ : congModNInt r₁ r₂ n := begin
            use (q₂ - q₁),
            rw ← sub_eq_iff_eq_add' at Ha₁ Ha₂,
            rw [← Ha₁, ← Ha₂],
            rw sub_mul,
            simp,
          end,

          have hr₁ : (- n : ℤ) < r₁ - r₂ := begin
            sorry,
          end,
          have hr₂ : r₁ - r₂ < n := begin
            sorry,
          end,

          have hr₃ : -1 < (r₁ - r₂) / n := begin
            sorry,
          end,
          have hr₄ : (r₁ - r₂) / n < 1 := begin
            sorry,
          end,

          have hr₅ : (r₁ - r₂) / n = 0 := by sorry,

          have hr₆ : r₁ - r₂ = 0 * n := by sorry,

          rw [zero_mul, sub_eq_zero] at hr₆,
          exact hr₆,
          },
        { sorry,}
  end

  #check nat.mod_le

end modular_arithmetic