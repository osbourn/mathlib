/-
Copyright (c) 2022 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/

import number_theory.arithmetic_function

open_locale big_operators

namespace nat
namespace arithmetic_function

variable (R : Type*)
variable {M : Type*}

section

variables [has_zero R] [add_comm_monoid M] [has_smul R M] [has_one M]

def is_dirichlet_inverse (f : arithmetic_function R) (g : arithmetic_function M) : Prop :=
f • g = 1

end

private lemma divisors_antidiagonal_erase_bounds {n : ℕ} {x : ℕ × ℕ}
  (h : x ∈ (divisors_antidiagonal n).erase ⟨1, n⟩) : x.2 < n :=
begin
  cases x with a b,
  change b < n,
  have h₁ : a * b = n := (mem_divisors_antidiagonal.mp (finset.mem_of_mem_erase h)).1,
  have h₂ : 0 < n := zero_lt_iff.mpr (mem_divisors_antidiagonal.mp (finset.mem_of_mem_erase h)).2,
  have h₃ : b ≤ n := le_of_dvd h₂ (dvd.intro_left a h₁),
  have h₄ : b ≠ n,
  { intro hb,
    rw hb at h₁,
    have : a = 1,
    { calc a = a * n / n : by rw nat.mul_div_cancel _ h₂
         ... = n / n : by rw h₁
         ... = 1 : by rw nat.div_self h₂ },
    rw [this, hb] at h,
    exact absurd h (finset.not_mem_erase (1, n) (divisors_antidiagonal n)) },
  exact ne.lt_of_le h₄ h₃
end

def gen_dirichlet_inverse_fn [field R] (f : arithmetic_function R) (h : f 1 ≠ 0) : ℕ → R
| 0 := 0
| 1 := 1 / (f 1)
| n := -1 / (f 1) * ∑ x : (divisors_antidiagonal n).erase ⟨1, n⟩,
  ( have x.val.2 < n := divisors_antidiagonal_erase_bounds x.property,
    (f x.val.1) * (gen_dirichlet_inverse_fn x.val.2))

def get_dirichlet_inverse [field R] (f : arithmetic_function R) (h : f 1 ≠ 0) :
  arithmetic_function R := ⟨gen_dirichlet_inverse_fn R f h, by unfold gen_dirichlet_inverse_fn⟩

lemma get_dirichlet_inverse_spec [field R] (f : arithmetic_function R) (h : f 1 ≠ 0) :
  is_dirichlet_inverse R f (get_dirichlet_inverse R f h) :=
begin
  sorry
end

end arithmetic_function
end nat
