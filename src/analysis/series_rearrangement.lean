import data.real.basic
import topology.algebra.infinite_sum.basic
import topology.instances.real
import analysis.normed.group.basic

def converges (series : ℕ → ℝ) : Prop := ∃ c : ℝ, filter.tendsto (λ k, (finset.range k).sum series) filter.at_top (nhds c)
def converges_absolutely (series : ℕ → ℝ) : Prop := converges (λ n, ‖(series n)‖)

noncomputable def pos_terms (a : ℕ → ℝ) : ℕ → ℝ := λ n, if 0 ≤ a n then a n else 0
noncomputable def neg_terms (a : ℕ → ℝ) : ℕ → ℝ := λ n, if 0 ≤ a n then 0 else a n

lemma pos_terms_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ (pos_terms a) n := sorry
lemma neg_terms_nonpos (a : ℕ → ℝ) (n : ℕ) : (neg_terms a) n ≤ 0 := sorry

lemma pos_terms_diverge {a : ℕ → ℝ} (h₁ : converges a) (h₂ : ¬converges_absolutely a)
  : filter.tendsto (λ k, (finset.range k).sum (pos_terms a)) filter.at_top filter.at_top := sorry
lemma neg_terms_diverge {a : ℕ → ℝ} (h₁ : converges a) (h₂ : ¬converges_absolutely a)
  : filter.tendsto (λ k, (finset.range k).sum (neg_terms a)) filter.at_top filter.at_bot := sorry

lemma pos_exceeds_value {a : ℕ → ℝ} (h₁ : converges a ∧ ¬converges_absolutely a) (M : ℝ)
  : ∃ p : ℕ, M < (finset.range p).sum (pos_terms a) :=
begin
  -- TODO: potentially use the fact that this statement is essentially the same as a tendsto
  -- statement involving M
  sorry
end

lemma neg_exceeds_value {a : ℕ → ℝ} (h₁ : converges a ∧ ¬converges_absolutely a) (M : ℝ)
  : ∃ p : ℕ, (finset.range p).sum (neg_terms a) < M := sorry

noncomputable def pos_least_exceeding {a : ℕ → ℝ} (h₁ : converges a ∧ ¬converges_absolutely a)
  (M : ℝ) : ℕ := nat.find (pos_exceeds_value h₁ M)

noncomputable def neg_least_exceeding {a : ℕ → ℝ} (h₁ : converges a ∧ ¬converges_absolutely a)
  (M : ℝ) : ℕ := nat.find (neg_exceeds_value h₁ M)

theorem riemann_rearrangement_theorem {series : ℕ → ℝ} (h₁ : converges series)
  (h₂ : ¬converges_absolutely series) (C : ℝ) : ∃ (p : ℕ → ℕ), function.bijective p ∧
    filter.tendsto (λ k, (finset.range k).sum (λ n, series (p n))) filter.at_top (nhds C) := sorry
