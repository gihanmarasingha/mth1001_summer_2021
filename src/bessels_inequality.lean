import analysis.normed_space.inner_product data.complex.is_R_or_C tactic

open_locale big_operators

variables {𝕜 E ι: Type*} [is_R_or_C 𝕜]  [inner_product_space 𝕜 E] [complete_space E]

open is_R_or_C 

include 𝕜

example (s : finset ι) (f : ι → E) : E :=  ∑ i in s, f i

example (y : E) : ∥y∥^2 = re (inner y y) := inner_product_space.norm_sq_eq_inner y

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

variables (s : finset ι) (f : ι → E) (x : E)

example : E := x -  ∑ i in s, ⟪x, f i⟫ • (f i)

example : ℝ := ∥ x -  ∑ i in s, ⟪x, f i⟫ • (f i) ∥

example : ℝ := ∥ x -  ∑ i in s, ⟪x, f i⟫ • (f i) ∥^2

example :
  ∥ x -  ∑ i in s, ⟪x, f i⟫ • (f i) ∥^2 = re ⟪x -  ∑ i in s, ⟪x, f i⟫ • (f i), x -  ∑ i in s, ⟪x, f i⟫ • (f i)⟫ :=
by { apply inner_product_space.norm_sq_eq_inner }

example : 𝕜 := ∑ i in s, ⟪x, f i⟫

example : 𝕜 := ∑ i in s, ⟪x, ⟪x, f i⟫ • (f i)⟫

example : ℝ := ∑ i in s, re ⟪x, ⟪x, f i⟫ • (f i)⟫

example : ℝ := ∥x∥^2

example : ℝ := ∑ i in s, (re ⟪x, f i⟫)^2

example : ℝ := ∥x∥^2 - 2 * ∑ i in s, re ⟪x, ⟪x, f i⟫ • (f i)⟫ 

example : ℝ := ∥x∥^2 - 2 * ∑ i in s, re ⟪x, ⟪x, f i⟫ • (f i)⟫ + ∑ i in s, (re ⟪x, f i⟫)^2

example (a b : 𝕜) : re (a + b) = re a + re b := by rw add_monoid_hom.map_add

example (a b : 𝕜) : re (a + b) = re a + re b := add_monoid_hom.map_add _ _ _

example (a b : 𝕜) : re (a - b) = re a - re b := by rw add_monoid_hom.map_sub

example (a b : 𝕜) : re (a - b) = re a - re b := add_monoid_hom.map_sub _ _ _

lemma foo {a b c d : ℝ} : a - b - c + d = a - (b + c - d) := by linarith

example {a b c d : ℝ} : a - b - c + d = (a - b) - c + d := rfl

example {a b c d : ℝ} : a - b - c + d = ((a - b) - c) + d := rfl

example {a b c d : ℝ} : a - b - c + d = ((a - b) - c) + d := rfl

example {p q r : ℝ} : p - q + r = p - (q - r) := by rw sub_add 

/- lemma bob : ∥ x -  ∑ i in s, ⟪x, f i⟫ • (f i) ∥^2 = ∥x∥^2 - ∑ i in s, (re ⟪x, f i⟫)^2 :=
begin
  conv_lhs { rw inner_product_space.norm_sq_eq_inner, },
  simp only [inner_sub_sub_self, add_monoid_hom.map_add, add_monoid_hom.map_sub],
  rw [←inner_product_space.norm_sq_eq_inner, sub_add, sub_sub],
  congr' 1,
  simp only [pow_two, finset.sum_congr],
end
 -/

omit 𝕜