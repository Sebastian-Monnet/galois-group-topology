import field_theory.adjoin
import algebra.big_operators.basic
import data.polynomial.algebra_map

noncomputable def alg_map (K L : Type*) [field K] [field L] [algebra K L] : polynomial(K) →+* polynomial(L) := polynomial.map_ring_hom (algebra_map K L)