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

open_locale classical


--def P (K L : Type*) [field K] [field L] [algebra K L] : 
--(intermediate_field K L) → (intermediate_field K L) → Prop := 
--λ E1 E2, E1 ≤ E2 ∧ finite_dimensional E1 E2



--subalgebra.inclusion h12 

@[instance]
def intermediate_field_le_module {K L : Type*} [field K] [field L] [algebra K L] {E1 E2 : intermediate_field K L} (h12 : E1 ≤ E2) : module ↥E1 ↥E2 :=
ring_hom.to_module (subalgebra.inclusion h12).to_ring_hom

/--def P {K L : Type*} [field K] [field L] [algebra K L] {E1 E2 : intermediate_field K L} (h12 : E1 ≤ E2) : 
Prop := finite_dimensional E1 E2-/

def P {K L : Type*} [field K] [field L] [algebra K L] {E1 E2 : intermediate_field K L} (h12 : E1 ≤ E2) : 
Prop := finite_dimensional (intermediate_field_le_module h12)