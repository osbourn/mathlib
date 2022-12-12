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

private lemma divisors_antidiagonal_erase_max {n : ℕ} {x : ℕ × ℕ}
  (h : x ∈ (divisors_antidiagonal n).erase ⟨1, n⟩) : x.2 < n :=
begin
  cases x with a b,
  change b < n,
  have h₁ : a * b = n := (mem_divisors_antidiagonal.mp (finset.mem_of_mem_erase h)).1,
  have h₂ : b ≤ n := sorry,
  have h₃ : b ≠ n := begin
    intro q,
    have : 0 < n := sorry,
    have : a = 1 := by {
      rw q at h₁,
      sorry
    },
    rw [this, q] at h,
    exact finset.not_mem_erase (1, n) (divisors_antidiagonal n) h
  end,
  exact ne.lt_of_le h₃ h₂
end

private def gen_dirichlet_inverse_fn [field R] (f : arithmetic_function R) (h : f 1 ≠ 0) : ℕ → R
| 0 := 0
| 1 := 1 / (f 1)
| n := -1 / (f 1) * ∑ x : ℕ × ℕ in (divisors_antidiagonal n).erase ⟨1, n⟩,
  ( have x.2 < n := sorry,
    (f x.1) * (gen_dirichlet_inverse_fn x.2))

def get_dirichlet_inverse [field R] (f : arithmetic_function R) (h : f 1 ≠ 0) :
  arithmetic_function R := ⟨gen_dirichlet_inverse_fn R f h, sorry⟩

lemma get_dirichlet_inverse_spec [field R] (f : arithmetic_function R) (h : f 1 ≠ 0) :
  is_dirichlet_inverse R f (get_dirichlet_inverse R f h) :=
begin
  sorry
end

end arithmetic_function
end nat
