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

noncomputable def neg_least_below (M : ℝ) : ℕ := nat.find (neg_exceeds_value hc hca M)

lemma pos_least_exceeding_spec (M : ℝ) : M < (finset.range $ pos_least_exceeding hc hca M).sum (pos_terms a) :=
nat.find_spec (pos_exceeds_value hc hca M)

lemma pos_least_exceeding_min (M : ℝ) {m : ℕ} (h : m < pos_least_exceeding hc hca M) :
  (finset.range m).sum (pos_terms a) ≤ M :=
begin
  have := nat.find_min (pos_exceeds_value hc hca M) h,
  change ¬M < (finset.range m).sum (pos_terms a) at this,
  exact le_of_not_lt this
end

noncomputable def gen_bounds (M : ℝ) : ℕ → (ℕ × ℕ)
| 0 := let p₁ : ℕ := pos_least_exceeding hc hca M in
       let q₂ : ℕ := neg_least_below hc hca (M - (finset.range p₁).sum (pos_terms a)) in
       (p₁, q₂)
| (step + 1) := let pₙ := pos_least_exceeding hc hca (M - (finset.range (gen_bounds step).snd).sum (neg_terms a)) in
                let qₙ := neg_least_below hc hca (M - (finset.range pₙ).sum (pos_terms a)) in
                (pₙ, qₙ)

noncomputable def p_bound (M : ℝ) (step : ℕ) : ℕ := (gen_bounds hc hca M step).fst
noncomputable def q_bound (M : ℝ) (step : ℕ) : ℕ := (gen_bounds hc hca M step).snd

lemma sums_gt_M (M : ℝ) (step : ℕ) : M < (finset.range (p_bound hc hca M (step + 1))).sum (pos_terms a) +
  (finset.range (q_bound hc hca M step)).sum (neg_terms a) :=
begin
  unfold p_bound,
  unfold gen_bounds,
  change M < (finset.range
      (pos_least_exceeding hc hca (M - (finset.range (q_bound hc hca M step)).sum (neg_terms a)))).sum
        (λ (x : ℕ), pos_terms a x) +
      (finset.range (q_bound hc hca M step)).sum (neg_terms a),
  have := pos_least_exceeding_spec hc hca (M - (finset.range (q_bound hc hca M step)).sum (neg_terms a)),
  have := add_lt_add_right this ((finset.range $ q_bound hc hca M step).sum (neg_terms a)),
  simpa using this,
end

lemma sums_previous_le_M (M : ℝ) (step : ℕ) : (finset.range $ (p_bound hc hca M (step + 1)) - 1).sum (pos_terms a) +
  (finset.range (q_bound hc hca M step)).sum (neg_terms a) ≤ M :=
begin
  --by_contra,
  --rw not_lt at h,
  unfold p_bound,
  unfold gen_bounds,
  change (finset.range
       (pos_least_exceeding hc hca (M - (finset.range (q_bound hc hca M step)).sum (neg_terms a)) - 1)).sum
      (pos_terms a) +
    (finset.range (q_bound hc hca M step)).sum (neg_terms a) ≤ M,
  sorry
end

theorem riemann_rearrangement_theorem {series : ℕ → ℝ} (h₁ : converges series)
  (h₂ : ¬converges_absolutely series) (C : ℝ) : ∃ (p : ℕ → ℕ), function.bijective p ∧
    filter.tendsto (λ k, (finset.range k).sum (λ n, series (p n))) filter.at_top (nhds C) := sorry
