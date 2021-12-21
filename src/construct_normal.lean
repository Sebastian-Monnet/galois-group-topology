import field_theory.adjoin
import algebra.big_operators.basic
import data.polynomial.algebra_map
import field_theory.normal

open_locale classical

noncomputable def min_polys {K E : Type*} [field K] [field E] [algebra K E] (h_findim : finite_dimensional K E) : finset (polynomial K) :=
finset.univ.image (minpoly K ∘ coe_fn(finite_dimensional.fin_basis K E))


def normal_closure {K E : Type*} [field K] [field E] [algebra K E] (h_findim : finite_dimensional K E) : Type* := 
polynomial.splitting_field (finset.prod (min_polys h_findim) (polynomial.map_ring_hom (algebra_map K E)))

instance {K E :Type*} [field K] [field E] [algebra K E] (h_findim : finite_dimensional K E) : field (normal_closure h_findim) :=
sorry

instance {K E :Type*} [field K] [field E] [algebra K E] (h_findim : finite_dimensional K E) : algebra K (normal_closure h_findim) :=
sorry

lemma is_normal {K E : Type*} [field K] [field E] [algebra K E] (h_findim : finite_dimensional K E) : normal K (normal_closure h_findim) := 
sorry 





