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

variables {a : ℕ → ℝ} (hc : converges a) (hca : ¬converges_absolutely a)

lemma pos_terms_diverge (h₁ : converges a) (h₂ : ¬converges_absolutely a)
  : filter.tendsto (λ k, (finset.range k).sum (pos_terms a)) filter.at_top filter.at_top := sorry
lemma neg_terms_diverge (h₁ : converges a) (h₂ : ¬converges_absolutely a)
  : filter.tendsto (λ k, (finset.range k).sum (neg_terms a)) filter.at_top filter.at_bot := sorry

lemma pos_exceeds_value (hc : converges a) (hca : ¬converges_absolutely a) (M : ℝ)
  : ∃ p : ℕ, M < (finset.range p).sum (pos_terms a) :=
begin
  -- TODO: potentially use the fact that this statement is essentially the same as a tendsto
  -- statement involving M
  sorry
end

lemma neg_exceeds_value (hc : converges a) (hca : ¬converges_absolutely a) (M : ℝ)
  : ∃ p : ℕ, (finset.range p).sum (neg_terms a) < M := sorry

noncomputable def pos_least_exceeding (M : ℝ) : ℕ := nat.find (pos_exceeds_value hc hca M)

noncomputable def neg_least_exceeding (M : ℝ) : ℕ := nat.find (neg_exceeds_value hc hca M)

noncomputable def gen_bounds (M : ℝ) : ℕ → (ℕ × ℕ)
| 0 := let p₁ : ℕ := pos_least_exceeding hc hca M in
            let q₂ : ℕ := neg_least_exceeding hc hca (M - (finset.range p₁).sum (pos_terms a)) in
            (p₁, q₂)
| (step + 1) := let (p_prev, q_prev) := gen_bounds step in
                let pₙ := pos_least_exceeding hc hca (M - (finset.range p_prev).sum (pos_terms a) - (finset.range q_prev).sum (neg_terms a)) in
                let qₙ := neg_least_exceeding hc hca (M - (finset.range pₙ).sum (pos_terms a) - (finset.range q_prev).sum (neg_terms a)) in
                (pₙ, qₙ)

theorem riemann_rearrangement_theorem {series : ℕ → ℝ} (h₁ : converges series)
  (h₂ : ¬converges_absolutely series) (C : ℝ) : ∃ (p : ℕ → ℕ), function.bijective p ∧
    filter.tendsto (λ k, (finset.range k).sum (λ n, series (p n))) filter.at_top (nhds C) := sorry
