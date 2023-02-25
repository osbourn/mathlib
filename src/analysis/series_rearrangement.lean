import data.real.basic
import topology.algebra.infinite_sum.basic
import topology.instances.real
import analysis.normed.group.basic

def converges (series : ℕ → ℝ) : Prop := ∃ c : ℝ, filter.tendsto series filter.at_top (nhds c)
def converges_absolutely (series : ℕ → ℝ) : Prop := converges (λ n, ‖(series n)‖)

noncomputable def pos_terms (a : ℕ → ℝ) : ℕ → ℝ := λ n, if 0 ≤ a n then a n else 0
noncomputable def neg_terms (a : ℕ → ℝ) : ℕ → ℝ := λ n, if 0 ≤ a n then 0 else a n

lemma pos_terms_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ (pos_terms a) n := sorry
lemma neg_terms_nonpos (a : ℕ → ℝ) (n : ℕ) : (neg_terms a) n ≤ 0 := sorry

theorem riemann_rearrangement_theorem {series : ℕ → ℝ} (h₁ : converges series)
  (h₂ : ¬converges_absolutely series) (C : ℝ) : ∃ (p : ℕ → ℕ), function.bijective p ∧
    filter.tendsto (λ n, series (p n)) filter.at_top (nhds C) := sorry
