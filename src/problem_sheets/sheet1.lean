import data.nat.basic tactic.induction


/-!
# Sheet 1: Primes and induction.
-/

/-!
## Question 1.

In each of the following cases, determine which integers `n` satisfy the stated
condition. Justify your answers.
-/

section question_1

variables m n a : ℕ

open nat

/-
We'll use the following results:
`le_antisymm`,
`le_of_dvd`,
`pos_of_dvd_of_pos`.
-/

example (h₁ : m ≤ n) (h₂ : n ≤ m) : m = n := le_antisymm h₁ h₂

example (h₁ : 0 < n) (h₂ : m ∣ n) : m ≤ n := le_of_dvd h₁ h₂

example (h₁ : m ∣ n) (h₂ : 0 < n) : 0 < m := pos_of_dvd_of_pos h₁ h₂

lemma q1_i : n ∣ 1 ↔ n = 1 :=
begin
  split, -- Split into proving `n ∣ 1 → n = 1` and `n = 1 → n ∣ 1`.
  -- First task it to prove `n ∣ 1 → n = 1`.
  { intro h, -- Assume `h : n ∣  1`. It suffices to prove `n = 1`.
    apply le_antisymm, -- It suffices to prove `n ≤ 1` and `1 ≤ n`.
    { -- Start by proving `n ≤ 1`.
      apply le_of_dvd, -- it suffices to prove `0 < 1` and `n ∣ 1`.
      { simp, },
      { exact h }, },
    { -- Now prove `1 ≤ n`.
      apply pos_of_dvd_of_pos h,
      simp, }, },
  -- Second task is to prove `n = 1 → n ∣ 1`.
  { intro h, rw h, },
end

/-
The `use` and `simp` and `trivial` tactics may help here.
It's more typical to write the following result as `1 ∣ n` rather than `1 ∣ n ↔ true`.
We've written the result this way so that we can `sorry` similar results in this question.
-/
lemma q1_ii : 1 ∣ n ↔ true :=
begin
  split,
  { intro h, sorry, },
  { intro h,
    dsimp [nat.has_dvd], -- By definition, we must show `∃ c, n = 1 * c`.
    sorry, },
end

-- `simp at ...` might be helpful below (replacing `...` with an appropriate hypothesis).
lemma q1_iii : 0 ∣ n ↔ n = 0 :=
begin
  split,
  { intro h, dsimp [nat.has_dvd] at h, -- By definition `h : ∃ c, n = 0 * c`.
    cases h with c h, -- Destructing, we have `c : ℕ` and `h : n = 0 * c`.
    sorry, },
  { sorry, },
end

lemma q1_iv : n ∣ 0 ↔ sorry :=
begin
  sorry,
end

lemma q1_v : n ∣ n ↔ sorry :=
begin
  sorry
end

-- The `specialize` tactic may be helpful here.
lemma q1_vi : (∀ a, a ∣ n) ↔ sorry :=
begin
  sorry
end

end question_1