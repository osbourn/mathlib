/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import topology.algebra.ring
import topology.algebra.group_with_zero
import topology.local_extr
import field_theory.subfield

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/


namespace topological_ring
open topological_space function
variables (R : Type*) [semiring R]

variables  [topological_space R]

/-- The induced topology on units of a topological semiring.
This is not a global instance since other topologies could be relevant. Instead there is a class
`induced_units` asserting that something equivalent to this construction holds. -/
def topological_space_units : topological_space Rˣ := induced (coe : Rˣ → R) ‹_›

/-- Asserts the topology on units is the induced topology.

 Note: this is not always the correct topology.
 Another good candidate is the subspace topology of $R \times R$,
 with the units embedded via $u \mapsto (u, u^{-1})$.
 These topologies are not (propositionally) equal in general. -/
class induced_units [t : topological_space $ Rˣ] : Prop :=
(top_eq : t = induced (coe : Rˣ → R) ‹_›)

variables [topological_space $ Rˣ]

lemma units_topology_eq [induced_units R] :
  ‹topological_space Rˣ› = induced (coe : Rˣ → R) ‹_› :=
induced_units.top_eq

lemma induced_units.continuous_coe [induced_units R] : continuous (coe : Rˣ → R) :=
(units_topology_eq R).symm ▸ continuous_induced_dom

lemma units_embedding [induced_units R] :
  embedding (coe : Rˣ → R) :=
{ induced := units_topology_eq R,
  inj := λ x y h, units.ext h }

instance top_monoid_units [topological_semiring R] [induced_units R] :
  has_continuous_mul Rˣ :=
⟨begin
  let mulR := (λ (p : R × R), p.1*p.2),
  let mulRx := (λ (p : Rˣ × Rˣ), p.1*p.2),
  have key : coe ∘ mulRx = mulR ∘ (λ p, (p.1.val, p.2.val)), from rfl,
  rw [continuous_iff_le_induced, units_topology_eq R, prod_induced_induced,
      induced_compose, key, ← induced_compose],
  apply induced_mono,
  rw ← continuous_iff_le_induced,
  exact continuous_mul,
end⟩
end topological_ring

variables {K : Type*} [division_ring K] [topological_space K]

/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_left₀ [has_continuous_mul K] {a : K} (ha : a ≠ 0) :
  filter.tendsto (λ x : K, a * x) (filter.cocompact K) (filter.cocompact K) :=
filter.tendsto_cocompact_mul_left (inv_mul_cancel ha)

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_right₀ [has_continuous_mul K] {a : K} (ha : a ≠ 0) :
  filter.tendsto (λ x : K, x * a) (filter.cocompact K) (filter.cocompact K) :=
filter.tendsto_cocompact_mul_right (mul_inv_cancel ha)

variables (K)

/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class topological_division_ring extends topological_ring K, has_continuous_inv₀ K : Prop

namespace topological_division_ring
open filter set
/-!
In this section, we show that units of a topological division ring endowed with the
induced topology form a topological group. These are not global instances because
one could want another topology on units. To turn on this feature, use:

```lean
local attribute [instance]
topological_semiring.topological_space_units topological_division_ring.units_top_group
```
-/

local attribute [instance] topological_ring.topological_space_units

@[priority 100] instance induced_units : topological_ring.induced_units K := ⟨rfl⟩

variables [topological_division_ring K]

lemma units_top_group : topological_group Kˣ :=
{ continuous_inv := begin
    rw continuous_iff_continuous_at,
    intros x,
    rw [continuous_at, nhds_induced, nhds_induced, tendsto_iff_comap,
      ←function.semiconj.filter_comap units.coe_inv _],
    apply comap_mono,
    rw [← tendsto_iff_comap, units.coe_inv],
    exact continuous_at_inv₀ x.ne_zero
  end,
  ..topological_ring.top_monoid_units K}

local attribute [instance] units_top_group

lemma continuous_units_inv : continuous (λ x : Kˣ, (↑(x⁻¹) : K)) :=
(topological_ring.induced_units.continuous_coe K).comp continuous_inv

end topological_division_ring

section subfield

variables {α : Type*} [field α] [topological_space α] [topological_division_ring α]

/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
def subfield.topological_closure (K : subfield α) : subfield α :=
{ carrier := closure (K : set α),
  inv_mem' :=
  begin
    intros x hx,
    by_cases h : x = 0,
    { rwa [h, inv_zero, ← h], },
    { convert mem_closure_image (continuous_at_inv₀ h) hx using 2,
      ext x, split,
      { exact λ hx, ⟨x⁻¹, ⟨K.inv_mem hx, inv_inv x⟩⟩, },
      { rintros ⟨y, ⟨hy, rfl⟩⟩, exact K.inv_mem hy, }},
  end,
  ..K.to_subring.topological_closure, }

lemma subfield.le_topological_closure (s : subfield α) :
  s ≤ s.topological_closure := subset_closure

lemma subfield.is_closed_topological_closure (s : subfield α) :
  is_closed (s.topological_closure : set α) := is_closed_closure

lemma subfield.topological_closure_minimal
  (s : subfield α) {t : subfield α} (h : s ≤ t) (ht : is_closed (t : set α)) :
  s.topological_closure ≤ t := closure_minimal h ht

end subfield

section affine_homeomorph
/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/
variables {𝕜 : Type*} [field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affine_homeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 :=
{ to_fun := λ x, a * x + b,
  inv_fun := λ y, (y - b) / a,
  left_inv := λ x, by { simp only [add_sub_cancel], exact mul_div_cancel_left x h, },
  right_inv := λ y, by { simp [mul_div_cancel' _ h], }, }

end affine_homeomorph

section local_extr

variables {α β : Type*} [topological_space α] [linear_ordered_semifield β] {a : α}
open_locale topological_space

lemma is_local_min.inv {f : α → β} {a : α} (h1 : is_local_min f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
  is_local_max f⁻¹ a :=
by filter_upwards [h1, h2] with z h3 h4 using (inv_le_inv h4 h2.self_of_nhds).mpr h3

end local_extr
