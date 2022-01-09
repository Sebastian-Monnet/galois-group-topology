import field_theory.galois 
import group_filter_basis


noncomputable def equiv_of_ultrafilter {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
(L ≃ₐ[K] L) :=
sorry

@[instance]
def krull_topology (K L : Type*) [field K] [field L] [algebra K L] :
topological_space (L ≃ₐ[K] L) := 
sorry

lemma krull_compact {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) 
(f : ultrafilter (L ≃ₐ[K] L)) 
(h_le_princ : ↑f ≤ filter.principal 
 (set.univ : set (L ≃ₐ[K] L))) :
is_compact (set.univ : set (L ≃ₐ[K] L)) :=
begin
  let σ := equiv_of_ultrafilter h_int h_splits f,
end

