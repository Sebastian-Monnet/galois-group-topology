import field_theory.adjoin
import algebra.big_operators.basic
import data.polynomial.algebra_map
import field_theory.normal

open_locale classical

noncomputable def min_polys {K E : Type*} [field K] [field E] [algebra K E] (h_findim : finite_dimensional K E) : finset (polynomial K) :=
finset.univ.image (minpoly K ∘ coe_fn(finite_dimensional.fin_basis K E))

def adj_roots {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} (h_findim : finite_dimensional K E) : intermediate_field K L := 
intermediate_field.adjoin K (polynomial.root_set (finset.prod (min_polys h_findim) (polynomial.map_ring_hom (algebra_map K E))) L)

lemma adj_roots_fin_dim {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} (h_findim : finite_dimensional K E) : finite_dimensional K (adj_roots h_findim) := 
begin
  sorry, 
end

lemma im_in_adj_roots {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} (h_findim : finite_dimensional K E) (σ : L →ₐ[K] L) : intermediate_field.map E σ ≤ adj_roots h_findim := 
begin
  sorry,
end