import tactic
import field_theory.galois
import data.set.basic
import algebra.group.basic
import ring_theory.tensor_product
import topology.algebra.filter_basis
import order.filter.bases 
import linear_algebra.finite_dimensional
import data.finset.basic 
import data.set.finite 
import data.polynomial.eval 

open_locale classical


-- Adjoin roots
noncomputable def root_finset {K : Type*} [field K] (p : polynomial K) (L : Type*) [field L] 
[algebra K L] : finset L := 
(p.map (algebra_map K L)).roots.to_finset

lemma root_finset_def {K : Type*} [field K] (p : polynomial K) (L : Type*) [field L] [algebra K L] 
{x : L}: x ∈ root_finset p L ↔ x ∈ (p.map (algebra_map K L)).roots.to_finset :=
begin
  refl,
end

noncomputable def min_polys {K E : Type*} [field K] [field E] [algebra K E] 
(h_findim : finite_dimensional K E) : finset (polynomial K) :=
finset.univ.image (minpoly K ∘ (finite_dimensional.fin_basis K E))

noncomputable def prod_min_polys {K E : Type*} [field K] [field E] [algebra K E] 
(h_findim : finite_dimensional K E) : polynomial K := 
finset.prod (min_polys h_findim) id


noncomputable def force_noncomputable {α : Sort*} (a : α) : α :=
  function.const _ a (classical.choice ⟨a⟩)

noncomputable def adj_roots {K L : Type} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
intermediate_field K L :=
force_noncomputable
intermediate_field.adjoin K (coe (root_finset (prod_min_polys h_findim) L) : set L)


lemma adj_roots_def {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
adj_roots h_findim = 
intermediate_field.adjoin K (coe (root_finset (prod_min_polys h_findim) L) : set L) :=
rfl 

lemma im_in_adj_roots {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} 
(h_findim : finite_dimensional K E) (σ : L →ₐ[K] L) : 
intermediate_field.map E σ ≤ adj_roots h_findim := 
begin
  sorry,
end